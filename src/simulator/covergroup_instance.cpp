#include "simulator/covergroup_instance.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <format>
#include <limits>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"
#include "simulator/covergroup_instance_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

namespace delta {

CovergroupFrame::CovergroupFrame(const CovergroupInstance& inst,
                                 SimContext& ctx, Arena& arena,
                                 const std::vector<CovergroupCall>& calls)
    : ctx_(ctx) {
  ctx.PushScope();
  for (const CovergroupCall& c : calls) {
    if (c.function != nullptr) BindFunctionArgs(c.function, c.call, ctx, arena);
  }
  ctx.EnterSubroutineScope({});
  for (const auto& [name, var] : inst.formals) ctx.BindLocalVariable(name, var);
  if (inst.owner != nullptr) {
    ctx.PushThis(inst.owner);
    ctx.PushMethodClass(inst.owner->type);
    pushed_this_ = true;
  }
}

CovergroupFrame::~CovergroupFrame() {
  if (pushed_this_) {
    ctx_.PopMethodClass();
    ctx_.PopThis();
  }
  ctx_.PopScope();
}

int64_t CovergroupIntOf(const Logic4Vec& v) {
  if (v.is_real) return static_cast<int64_t>(std::llround(RealVecToDouble(v)));
  return SelectBoundValue(v);
}

double CovergroupRealOf(const Logic4Vec& v) {
  if (v.is_real) return RealVecToDouble(v);
  return static_cast<double>(SelectBoundValue(v));
}

int64_t CovergroupInt(const Expr* e, SimContext& ctx, Arena& arena) {
  return CovergroupIntOf(EvalExpr(e, ctx, arena));
}

double CovergroupReal(const Expr* e, SimContext& ctx, Arena& arena) {
  return CovergroupRealOf(EvalExpr(e, ctx, arena));
}

CoverValueRange PointTypeBounds(const SampledCoverpoint& point) {
  if (point.width == 0 || point.width >= 64) {
    return {point.is_signed ? std::numeric_limits<int64_t>::min() : 0,
            std::numeric_limits<int64_t>::max()};
  }
  if (point.is_signed) {
    int64_t half = int64_t{1} << (point.width - 1);
    return {-half, half - 1};
  }
  return {0, static_cast<int64_t>((uint64_t{1} << point.width) - 1)};
}

int64_t ConvertToPointType(const Logic4Vec& v, const SampledCoverpoint& point) {
  return ConvertToPointType(
      v.is_real ? static_cast<uint64_t>(std::llround(RealVecToDouble(v)))
                : v.ToUint64(),
      point);
}

int64_t ConvertToPointType(uint64_t bits, const SampledCoverpoint& point) {
  if (point.width == 0 || point.width >= 64) return static_cast<int64_t>(bits);
  uint64_t mask = (uint64_t{1} << point.width) - 1;
  bits &= mask;
  if (point.is_signed && (bits >> (point.width - 1)) != 0) bits |= ~mask;
  return static_cast<int64_t>(bits);
}

namespace {

// A function standing for a formal list of the covergroup, so that the
// actuals of a call are bound to it as to a function's (§19.3, §19.8.1).
const ModuleItem* FormalsFunction(std::string_view name,
                                  const std::vector<FunctionArg>& formals,
                                  Arena& arena) {
  if (formals.empty()) return nullptr;
  auto* function = arena.Create<ModuleItem>();
  function->kind = ModuleItemKind::kFunctionDecl;
  function->name = name;
  function->func_args = formals;
  function->is_automatic = true;
  return function;
}

// A call of no arguments, whose binding gives each formal its default.
const Expr* EmptyCall(Arena& arena) {
  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  return call;
}

// §19.5: the name a coverpoint goes by, its label or, unlabelled, the variable
// its expression names; any other is given its position.
std::string CoverpointName(const CoverPointDecl& cp, size_t index) {
  if (!cp.label.empty()) return std::string(cp.label);
  if (cp.expr->kind == ExprKind::kIdentifier) return std::string(cp.expr->text);
  return std::format("__coverpoint_{}", index);
}

// §19.5: a coverpoint with a data type samples its expression as that type,
// and one without as the self-determined type of the expression.
void SetPointType(SampledCoverpoint& point, const CoverPointDecl& decl,
                  SimContext& ctx, Arena& arena) {
  if (decl.has_data_type) {
    point.width = DeclaredTypeWidth(decl.data_type, ctx);
    point.is_signed = DeclaredTypeIsSigned(decl.data_type, ctx);
    point.is_real = DeclaredTypeIsReal(decl.data_type, ctx);
    point.is_four_state = DeclaredTypeIs4State(decl.data_type, ctx);
    point.enum_type = EnumTypeOfDataType(decl.data_type, ctx);
    return;
  }
  Logic4Vec v = EvalExpr(decl.expr, ctx, arena);
  point.width = v.width;
  point.is_signed = v.is_signed;
  point.is_real = v.is_real;
  point.enum_type = EnumTypeOfExpr(decl.expr, ctx, arena);
}

// §19.5.3: whether the bits of a sampled value that the coverpoint's type
// keeps hold an x or z.
bool SampleHasUnknownBits(const Logic4Vec& v, const SampledCoverpoint& point) {
  if (v.is_real || !point.is_four_state) return false;
  uint32_t width = point.width == 0 ? v.width : std::min(point.width, v.width);
  for (uint32_t i = 0; i < v.nwords && i * 64 < width; ++i) {
    uint32_t bits = std::min<uint32_t>(64, width - (i * 64));
    uint64_t mask = bits == 64 ? ~uint64_t{0} : (uint64_t{1} << bits) - 1;
    if ((v.words[i].bval & mask) != 0) return true;
  }
  return false;
}

// §19.3: the instance's formals, which the frame of its construction bound to
// the actuals of new().
void KeepFormals(CovergroupInstance& inst, SimContext& ctx) {
  for (const FunctionArg& formal : inst.decl->formals) {
    Variable* var = ctx.FindLocalVariable(formal.name);
    if (var != nullptr) inst.formals.emplace_back(formal.name, var);
  }
}

// §19.7: the covergroup's option assignments are applied first, so that the
// options which default the coverpoints' and crosses' (§19.7, Table 19-2)
// are in place when those are built; the crosses follow every coverpoint.
void BuildItems(CovergroupInstance& inst, SimContext& ctx, Arena& arena) {
  const CovergroupDecl& decl = *inst.decl;
  for (const CoverageSpecOrOption& item : decl.items) {
    if (item.kind == CoverageSpecKind::kOption) {
      ApplyGroupOption(inst, item.option, ctx, arena);
    }
  }
  for (size_t i = 0; i < decl.items.size(); ++i) {
    if (decl.items[i].kind == CoverageSpecKind::kCoverPoint) {
      BuildCoverpoint(inst, *decl.items[i].cover_point, i, ctx, arena);
    }
  }
  for (size_t i = 0; i < decl.items.size(); ++i) {
    if (decl.items[i].kind == CoverageSpecKind::kCoverCross) {
      BuildCross(inst, *decl.items[i].cover_cross, i, ctx, arena);
    }
  }
}

void SetGuard(const Expr* iff, bool& has_guard, bool& guard_value,
              SimContext& ctx, Arena& arena) {
  has_guard = iff != nullptr;
  guard_value = !has_guard || EvalExpr(iff, ctx, arena).IsTruthy();
}

void SetGuards(CovergroupInstance& inst, SimContext& ctx, Arena& arena) {
  for (SampledCoverpoint& point : inst.points) {
    CoverPoint* cp = point.point;
    SetGuard(point.iff, cp->has_iff_guard, cp->iff_guard_value, ctx, arena);
    for (const auto& [index, guard] : point.bin_guards) {
      CoverBin& bin = cp->bins[index];
      SetGuard(guard, bin.has_iff_guard, bin.iff_guard_value, ctx, arena);
    }
  }
  for (SampledCross& sampled : inst.crosses) {
    CrossCover& cross = inst.group->crosses[sampled.index];
    SetGuard(sampled.iff, cross.has_iff_guard, cross.iff_guard_value, ctx,
             arena);
    for (const auto& [index, guard] : sampled.bin_guards) {
      CrossBin& bin = cross.bins[index];
      SetGuard(guard, bin.has_iff_guard, bin.iff_guard_value, ctx, arena);
    }
  }
}

struct SampledValues {
  std::vector<std::pair<std::string, int64_t>> integral;
  std::vector<std::pair<std::string, double>> real;

  std::string Of(const std::string& name) const {
    for (const auto& [n, v] : integral) {
      if (n == name) return std::to_string(v);
    }
    for (const auto& [n, v] : real) {
      if (n == name) return std::format("{}", v);
    }
    return {};
  }
};

SampledValues ReadPoints(const CovergroupInstance& inst, SimContext& ctx,
                         Arena& arena) {
  SampledValues values;
  for (const SampledCoverpoint& point : inst.points) {
    Logic4Vec v = EvalExpr(point.expr, ctx, arena);
    const std::string& name = point.point->name;
    if (point.is_real) {
      values.real.emplace_back(
          name, v.is_real ? RealVecToDouble(v)
                          : static_cast<double>(ConvertToPointType(v, point)));
    } else {
      point.point->sample_has_xz = SampleHasUnknownBits(v, point);
      values.integral.emplace_back(name, ConvertToPointType(v, point));
    }
  }
  return values;
}

// §19.6.3: a sampled cross product an illegal_bins selection selects is a
// run-time error, unless the cross's guard is false.
void ReportIllegalCrossProducts(const CovergroupInstance& inst, SourceLoc loc,
                                SimContext& ctx) {
  for (const SampledCross& sampled : inst.crosses) {
    const CrossCover& cross = inst.group->crosses[sampled.index];
    if (cross.has_iff_guard && !cross.iff_guard_value) continue;
    for (const IllegalCrossProducts& sel : sampled.illegal) {
      bool hit = std::ranges::any_of(sel.tuples, [&](const auto& tuple) {
        return CoverageDB::CrossTupleSampled(inst.group, &cross, tuple);
      });
      if (hit) {
        ctx.GetDiag().Error(
            loc,
            std::format("sampled values of cross '{}' fall in its illegal "
                        "bins '{}'",
                        cross.name, sel.bins_name),
            Subclause("19.6.3"));
      }
    }
  }
}

// §19.8: samples the instance, reporting a value an illegal_bins holds
// (§19.5.6) and a tuple an illegal_bins selection of a cross covers (§19.6.3)
// as run-time errors at the call that sampled it. §19.8.1: the arguments of
// the call are bound to the formals of `with function sample`.
void SampleInstance(CovergroupInstance& inst, const Expr* call, SimContext& ctx,
                    Arena& arena) {
  if (!inst.group->collecting) return;
  CovergroupFrame frame(inst, ctx, arena, {{inst.sample_function, call}});
  SetGuards(inst, ctx, arena);
  SampledValues values = ReadPoints(inst, ctx, arena);
  std::vector<uint64_t> violations;
  violations.reserve(inst.group->coverpoints.size());
  for (const CoverPoint& cp : inst.group->coverpoints) {
    violations.push_back(cp.illegal_violations);
  }
  ctx.CoverageData().Sample(inst.group, values.integral, values.real);
  size_t index = 0;
  for (const CoverPoint& cp : inst.group->coverpoints) {
    if (cp.illegal_violations > violations[index++]) {
      ctx.GetDiag().Error(
          call->range.start,
          std::format("sampled value {} of coverpoint '{}' falls in an "
                      "illegal bin",
                      values.Of(cp.name), cp.name),
          Subclause("19.5.6"));
    }
  }
  ReportIllegalCrossProducts(inst, call->range.start, ctx);
}

// What a call or an option read reaches: an instance, or one of its
// coverpoints or crosses.
struct CovergroupTarget {
  CovergroupInstance* inst = nullptr;
  SampledCoverpoint* point = nullptr;
  SampledCross* cross = nullptr;
};

// The object an expression naming a class handle holds; null where it names
// none. Only a name is read, so that no expression is evaluated for its side
// effects.
ClassObject* ObjectNamed(const Expr* e, SimContext& ctx, Arena& arena) {
  if (e->kind != ExprKind::kIdentifier) return nullptr;
  if (e->text == "this") return ctx.CurrentThis();
  if (ctx.GetVariableClassType(e->text).empty()) return nullptr;
  return ctx.GetClassObject(EvalExpr(e, ctx, arena).ToUint64());
}

// The instance a receiver names: a variable holding one, an embedded
// covergroup of the object whose method is running, or `h.cg`, the embedded
// covergroup `cg` of the object `h` holds.
CovergroupInstance* InstanceNamed(const Expr* e, SimContext& ctx,
                                  Arena& arena) {
  CovergroupTable& table = ctx.Covergroups();
  if (e->kind == ExprKind::kIdentifier) {
    ClassObject* self = ctx.CurrentThis();
    if (self != nullptr && table.Embedded(self->type, e->text) != nullptr) {
      return table.FindEmbedded(self, e->text);
    }
    return table.Find(e->text, ctx);
  }
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution) {
    return nullptr;
  }
  ClassObject* owner = ObjectNamed(e->lhs, ctx, arena);
  if (owner == nullptr) return nullptr;
  return table.FindEmbedded(owner, e->rhs->text);
}

CovergroupTarget TargetNamed(const Expr* e, SimContext& ctx, Arena& arena) {
  if (CovergroupInstance* inst = InstanceNamed(e, ctx, arena)) {
    return {inst, nullptr, nullptr};
  }
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution) return {};
  CovergroupInstance* inst = InstanceNamed(e->lhs, ctx, arena);
  if (inst == nullptr) return {};
  std::string_view item = e->rhs->text;
  for (SampledCoverpoint& point : inst->points) {
    if (point.point->name == item) return {inst, &point, nullptr};
  }
  for (SampledCross& cross : inst->crosses) {
    if (inst->group->crosses[cross.index].name == item) {
      return {inst, nullptr, &cross};
    }
  }
  return {};
}

// §19.8: the optional ref-int pair of get_coverage() and get_inst_coverage()
// receives the covered and the defined bins.
void WriteCounts(const Expr* call, int32_t covered, int32_t total,
                 SimContext& ctx, Arena& arena) {
  if (call->args.size() != 2) return;
  std::array<int32_t, 2> counts = {covered, total};
  for (size_t i = 0; i < 2; ++i) {
    Variable* v = ctx.FindVariable(call->args[i]->text);
    if (v != nullptr) {
      v->value = MakeLogic4VecVal(arena, v->value.width,
                                  static_cast<uint64_t>(counts[i]));
    }
  }
}

bool MergesInstances(const CovergroupInstance& inst) {
  return inst.group->type_option.merge_instances;
}

// §19.11.3: the coverage of the covergroup type, over every instance of it,
// with the covered and defined bins of them all.
double TypeCoverage(const CovergroupDecl* decl, bool merge, SimContext& ctx,
                    int32_t& covered, int32_t& total) {
  std::vector<const CoverGroup*> instances =
      ctx.Covergroups().InstancesOf(decl);
  covered = 0;
  total = 0;
  for (const CoverGroup* group : instances) {
    int32_t n = 0;
    int32_t t = 0;
    CoverageDB::GetCoverage(group, n, t);
    covered += n;
    total += t;
  }
  return CoverageDB::ComputeTypeCoverage(instances, merge);
}

// The same item of every instance of the instance's type: its coverpoint or
// cross of one name.
std::vector<const CoverPoint*> PointsOfType(const CovergroupInstance& inst,
                                            const std::string& name,
                                            SimContext& ctx) {
  std::vector<const CoverPoint*> found;
  for (const CoverGroup* group : ctx.Covergroups().InstancesOf(inst.decl)) {
    for (const CoverPoint& cp : group->coverpoints) {
      if (cp.name == name) found.push_back(&cp);
    }
  }
  return found;
}

std::vector<const CrossCover*> CrossesOfType(const CovergroupInstance& inst,
                                             const std::string& name,
                                             SimContext& ctx) {
  std::vector<const CrossCover*> found;
  for (const CoverGroup* group : ctx.Covergroups().InstancesOf(inst.decl)) {
    for (const CrossCover& cross : group->crosses) {
      if (cross.name == name) found.push_back(&cross);
    }
  }
  return found;
}

// §19.8 and §19.11: get_coverage() answers for the covergroup type, and
// get_inst_coverage() for the instance, or for its type where the
// merge_instances type option is set and the get_inst_coverage option is not
// (§19.7, Table 19-1); through a coverpoint or a cross, each answers for that
// item.
Logic4Vec ReportCoverage(const CovergroupTarget& target, const Expr* call,
                         bool instance, SimContext& ctx, Arena& arena) {
  int32_t covered = 0;
  int32_t total = 0;
  double coverage = 0.0;
  const CovergroupInstance& inst = *target.inst;
  bool merge = MergesInstances(inst);
  if (target.point != nullptr) {
    const CoverPoint* cp = target.point->point;
    coverage = CoverageDB::GetPointCoverage(cp, covered, total);
    if (!instance) {
      coverage = CoverageDB::ComputePointTypeCoverage(
          PointsOfType(inst, cp->name, ctx), merge);
    }
  } else if (target.cross != nullptr) {
    const CrossCover& cross = inst.group->crosses[target.cross->index];
    coverage = CoverageDB::GetCrossCoverage(&cross, covered, total);
    if (!instance) {
      coverage = CoverageDB::ComputeCrossTypeCoverage(
          CrossesOfType(inst, cross.name, ctx), merge);
    }
  } else if (instance && (!merge || inst.group->options.get_inst_coverage)) {
    coverage = CoverageDB::GetInstCoverage(inst.group, covered, total);
  } else {
    coverage = TypeCoverage(inst.decl, merge, ctx, covered, total);
  }
  WriteCounts(call, covered, total, ctx, arena);
  return MakeRealVec(arena, coverage, 64);
}

Logic4Vec RunGroupMethod(std::string_view method, CovergroupInstance& inst,
                         const Expr* call, SimContext& ctx, Arena& arena) {
  if (method == "sample") {
    SampleInstance(inst, call, ctx, arena);
  } else if (method == "start") {
    CoverageDB::Start(inst.group);
  } else if (method == "stop") {
    CoverageDB::Stop(inst.group);
  } else if (method == "set_inst_name" && !call->args.empty()) {
    CoverageDB::SetInstName(
        inst.group, Logic4VecToString(EvalExpr(call->args[0], ctx, arena)));
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

bool IsCovergroupMethod(std::string_view method) {
  return method == "sample" || method == "get_coverage" ||
         method == "get_inst_coverage" || method == "set_inst_name" ||
         method == "start" || method == "stop";
}

// §19.8: `cg::get_coverage()`, the coverage of the covergroup type `cg`.
bool TryEvalTypeCoverageCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out) {
  const Expr* access = expr->lhs;
  if (access->rhs->text != "get_coverage" ||
      access->lhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const ModuleItem* item = ctx.FindLetDecl(access->lhs->text);
  if (item == nullptr || item->kind != ModuleItemKind::kCovergroupDecl) {
    return false;
  }
  int32_t covered = 0;
  int32_t total = 0;
  std::vector<const CoverGroup*> instances =
      ctx.Covergroups().InstancesOf(item->covergroup);
  bool merge = !instances.empty() && instances[0]->type_option.merge_instances;
  double coverage = TypeCoverage(item->covergroup, merge, ctx, covered, total);
  WriteCounts(expr, covered, total, ctx, arena);
  out = MakeRealVec(arena, coverage, 64);
  return true;
}

// §19.3 and §19.4: where an assignment of `new` to `lhs` builds its
// instance; a site of no covergroup where `lhs` is of no covergroup type.
CovergroupSite NewSiteOf(const Expr* lhs, SimContext& ctx, Arena& arena) {
  ClassObject* owner = nullptr;
  std::string_view name;
  if (lhs->kind == ExprKind::kIdentifier) {
    owner = ctx.CurrentThis();
    name = lhs->text;
  } else if (lhs->kind == ExprKind::kMemberAccess &&
             !lhs->is_scope_resolution) {
    owner = ObjectNamed(lhs->lhs, ctx, arena);
    if (owner == nullptr) return {};
    name = lhs->rhs->text;
  } else {
    return {};
  }
  if (owner != nullptr) {
    if (const CovergroupDecl* decl =
            ctx.Covergroups().Embedded(owner->type, name)) {
      return {CovergroupTable::EmbeddedKey(owner, name), decl, owner};
    }
    if (lhs->kind != ExprKind::kIdentifier) return {};
  }
  const auto* declared = ctx.Covergroups().FindDeclared(name, ctx);
  if (declared == nullptr) return {};
  return {declared->first, declared->second, nullptr};
}

// §19.3 with §19.4: the process sampling an embedded covergroup at each
// occurrence of its clocking event, as an always procedure would.
SimCoroutine EmbeddedSamplingCoroutine(const Stmt* wait, SimContext& ctx,
                                       Arena& arena) {
  while (!ctx.StopRequested()) {
    if (co_await ExecStmt(wait, ctx, arena) != StmtResult::kDone) break;
  }
}

// §19.3: the statement an embedded covergroup's sampling process repeats,
// `@(clocking_event) name.sample();`.
const Stmt* EmbeddedSamplingWait(const CovergroupDecl& decl, Arena& arena) {
  auto* access = arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = arena.Create<Expr>();
  access->lhs->kind = ExprKind::kIdentifier;
  access->lhs->text = decl.name;
  access->rhs = arena.Create<Expr>();
  access->rhs->kind = ExprKind::kIdentifier;
  access->rhs->text = "sample";
  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->lhs = access;
  auto* sample = arena.Create<Stmt>();
  sample->kind = StmtKind::kExprStmt;
  sample->expr = call;
  auto* wait = arena.Create<Stmt>();
  wait->kind = StmtKind::kEventControl;
  wait->events = decl.event.clocking;
  wait->body = sample;
  return wait;
}

// §19.3 with §19.4: an embedded covergroup with a clocking event is sampled
// at each occurrence of the event for each object whose instance of it is
// built, by a process of its own that waits on the event, `this` the object,
// and calls sample() on the object's instance. The process stands in the
// instance and generate blocks of the one building the instance, where the
// event's names resolve.
void StartEmbeddedSampling(const CovergroupInstance& inst, SimContext& ctx,
                           Arena& arena) {
  auto* p = arena.Create<Process>();
  p->kind = ProcessKind::kAlways;
  if (const Process* building = ctx.CurrentProcess()) {
    p->inst_prefix = building->inst_prefix;
    p->gen_prefixes = building->gen_prefixes;
    p->gen_block_name = building->gen_block_name;
    p->program_block_id = building->program_block_id;
  }
  p->saved_this_stack = {inst.owner};
  p->saved_method_class_stack = {inst.owner->type};
  p->rng_seed = ctx.DrawSeedForChild();
  p->coro = EmbeddedSamplingCoroutine(EmbeddedSamplingWait(*inst.decl, arena),
                                      ctx, arena)
                .Release();
  auto* start = ctx.GetScheduler().GetEventPool().Acquire();
  start->callback = [p, &ctx]() {
    if (!p->active) return;
    ctx.SetCurrentProcess(p);
    p->Resume();
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kActive, start);
}

}  // namespace

void BuildCoverpoint(CovergroupInstance& inst, const CoverPointDecl& decl,
                     size_t index, SimContext& ctx, Arena& arena) {
  const CoverGroup& group = *inst.group;
  SampledCoverpoint point;
  point.point =
      CoverageDB::AddCoverPoint(inst.group, CoverpointName(decl, index));
  point.expr = decl.expr;
  point.iff = decl.iff;
  SetPointType(point, decl, ctx, arena);
  point.option.at_least = group.options.at_least;
  point.option.auto_bin_max = group.options.auto_bin_max;
  point.option.detect_overlap = group.options.detect_overlap;
  point.type_option.real_interval = group.type_option.real_interval;
  for (const BinsOrOptions& bins : decl.bins) {
    if (bins.kind == BinsOrOptionsKind::kOption) {
      ApplyPointOption(point, bins.option, ctx, arena);
    }
  }
  point.point->auto_bin_count =
      static_cast<uint32_t>(std::max(0, point.option.auto_bin_max));
  point.point->weight = point.option.weight;
  inst.points.push_back(std::move(point));
  BuildCoverpointBins(inst, inst.points.back(), decl, ctx, arena);
}

CovergroupInstance* CovergroupTable::Create(std::string_view key) {
  return &instances_[std::string(key)];
}

CovergroupInstance* CovergroupTable::Find(std::string_view name,
                                          const SimContext& ctx) {
  for (const std::string& key : ctx.ScopedObjectKeys(name)) {
    auto it = instances_.find(key);
    if (it != instances_.end()) return &it->second;
  }
  return nullptr;
}

std::string CovergroupTable::EmbeddedKey(const ClassObject* owner,
                                         std::string_view name) {
  return std::format("{}.{}", static_cast<const void*>(owner), name);
}

namespace {

// §19.4: every covergroup `type` and the classes it derives from embed.
std::vector<std::pair<std::string_view, const CovergroupDecl*>>
EmbeddedCovergroups(const ClassTypeInfo* type) {
  std::vector<std::pair<std::string_view, const CovergroupDecl*>> embedded;
  for (; type != nullptr; type = type->parent) {
    if (type->decl == nullptr) continue;
    for (const ClassMember* member : type->decl->members) {
      if (member->kind == ClassMemberKind::kCovergroup) {
        embedded.emplace_back(member->name, member->covergroup);
      }
    }
  }
  return embedded;
}

}  // namespace

const CovergroupDecl* CovergroupTable::Embedded(const ClassTypeInfo* type,
                                                std::string_view name) {
  auto [it, inserted] = embedded_.try_emplace(type);
  if (inserted) it->second = EmbeddedCovergroups(type);
  for (const auto& [embedded, decl] : it->second) {
    if (embedded == name) return decl;
  }
  return nullptr;
}

CovergroupInstance* CovergroupTable::FindEmbedded(const ClassObject* owner,
                                                  std::string_view name) {
  auto it = instances_.find(EmbeddedKey(owner, name));
  return it != instances_.end() ? &it->second : nullptr;
}

void CovergroupTable::Declare(std::string_view key,
                              const CovergroupDecl* decl) {
  declared_[std::string(key)] = decl;
}

const std::pair<const std::string, const CovergroupDecl*>*
CovergroupTable::FindDeclared(std::string_view name,
                              const SimContext& ctx) const {
  for (const std::string& key : ctx.ScopedObjectKeys(name)) {
    auto it = declared_.find(key);
    if (it != declared_.end()) return &*it;
  }
  return nullptr;
}

void CovergroupTable::Record(const CovergroupInstance& inst) {
  built_.emplace_back(inst.decl, inst.group);
}

std::vector<const CoverGroup*> CovergroupTable::InstancesOf(
    const CovergroupDecl* decl) const {
  std::vector<const CoverGroup*> groups;
  for (const auto& [d, group] : built_) {
    if (d == decl) groups.push_back(group);
  }
  return groups;
}

CovergroupInstance* BuildCovergroupInstance(const CovergroupSite& site,
                                            const Expr* new_call,
                                            SimContext& ctx, Arena& arena) {
  const CovergroupDecl& decl = *site.decl;
  bool first_for_owner =
      site.owner != nullptr &&
      ctx.Covergroups().FindEmbedded(site.owner, decl.name) == nullptr;
  CovergroupInstance* inst = ctx.Covergroups().Create(site.key);
  *inst = CovergroupInstance{};
  inst->decl = &decl;
  inst->owner = site.owner;
  inst->group = ctx.CoverageData().CreateGroup(site.key);
  inst->group->options.name = site.key;
  inst->sample_function =
      FormalsFunction("sample", decl.event.sample_formals, arena);
  const Expr* call = new_call != nullptr ? new_call : EmptyCall(arena);
  CovergroupFrame frame(
      *inst, ctx, arena,
      {{FormalsFunction(decl.name, decl.formals, arena), call},
       {inst->sample_function, EmptyCall(arena)}});
  KeepFormals(*inst, ctx);
  BuildItems(*inst, ctx, arena);
  ctx.Covergroups().Record(*inst);
  if (first_for_owner && decl.event.kind == CoverageEventKind::kClocking) {
    StartEmbeddedSampling(*inst, ctx, arena);
  }
  return inst;
}

void CreateCovergroupForVar(std::string_view name, const RtlirVariable& var,
                            SimContext& ctx, Arena& arena) {
  ctx.Covergroups().Declare(name, var.covergroup);
  const Expr* init = var.init_expr;
  if (init != nullptr && init->kind == ExprKind::kCall && init->text == "new") {
    BuildCovergroupInstance({std::string(name), var.covergroup, nullptr}, init,
                            ctx, arena);
  }
}

bool TryCovergroupNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  const Expr* rhs = stmt->rhs;
  if (stmt->lhs == nullptr || rhs == nullptr || rhs->kind != ExprKind::kCall ||
      rhs->text != "new") {
    return false;
  }
  CovergroupSite site = NewSiteOf(stmt->lhs, ctx, arena);
  if (site.decl == nullptr) return false;
  BuildCovergroupInstance(site, rhs, ctx, arena);
  return true;
}

bool TryCovergroupOptionAssign(const Stmt* stmt, SimContext& ctx,
                               Arena& arena) {
  const Expr* lhs = stmt->lhs;
  if (lhs == nullptr || stmt->rhs == nullptr ||
      lhs->kind != ExprKind::kMemberAccess || lhs->rhs == nullptr ||
      lhs->lhs == nullptr || lhs->lhs->kind != ExprKind::kMemberAccess ||
      lhs->lhs->rhs == nullptr || lhs->lhs->rhs->text != "option" ||
      ctx.Covergroups().Empty()) {
    return false;
  }
  CovergroupTarget target = TargetNamed(lhs->lhs->lhs, ctx, arena);
  if (target.inst == nullptr) return false;
  Logic4Vec value = EvalExpr(stmt->rhs, ctx, arena);
  std::string_view member = lhs->rhs->text;
  if (target.point != nullptr) {
    WritePointOption(*target.point, member, value);
  } else if (target.cross != nullptr) {
    WriteCrossOption(target.inst->group->crosses[target.cross->index], member,
                     value);
  } else {
    WriteGroupOption(*target.inst->group, member, value);
  }
  return true;
}

bool TryEvalCovergroupMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  const Expr* access = expr->lhs;
  if (ctx.Covergroups().Empty() || access == nullptr ||
      access->kind != ExprKind::kMemberAccess || access->rhs == nullptr ||
      !IsCovergroupMethod(access->rhs->text)) {
    return false;
  }
  if (access->is_scope_resolution) {
    return TryEvalTypeCoverageCall(expr, ctx, arena, out);
  }
  CovergroupTarget target = TargetNamed(access->lhs, ctx, arena);
  if (target.inst == nullptr) return false;
  std::string_view method = access->rhs->text;
  if (method == "get_coverage" || method == "get_inst_coverage") {
    out =
        ReportCoverage(target, expr, method == "get_inst_coverage", ctx, arena);
    return true;
  }
  if (target.point != nullptr || target.cross != nullptr) return false;
  out = RunGroupMethod(method, *target.inst, expr, ctx, arena);
  return true;
}

bool TryEvalCovergroupOptionRead(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  const Expr* access = expr->lhs;
  if (expr->rhs == nullptr || access == nullptr ||
      access->kind != ExprKind::kMemberAccess || access->rhs == nullptr ||
      (access->rhs->text != "option" && access->rhs->text != "type_option") ||
      ctx.Covergroups().Empty()) {
    return false;
  }
  CovergroupTarget target = TargetNamed(access->lhs, ctx, arena);
  if (target.inst == nullptr) return false;
  bool type_option = access->rhs->text == "type_option";
  std::string_view member = expr->rhs->text;
  if (target.point != nullptr) {
    return ReadPointOption(*target.point, type_option, member, arena, out);
  }
  if (target.cross != nullptr) {
    return ReadCrossOption(target.inst->group->crosses[target.cross->index],
                           type_option, member, arena, out);
  }
  return ReadGroupOption(*target.inst->group, type_option, member, arena, out);
}

}  // namespace delta
