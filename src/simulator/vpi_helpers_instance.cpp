#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <functional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_primitives.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_specify.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_timing_check.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_alloc_scheme.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_delay_devices.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_pool_keeper.h"
#include "simulator/vpi_source_delay.h"
#include "simulator/vpi_user.h"

namespace delta {

VpiContext::~VpiContext() {
  for (auto* obj : all_objects_) {
    delete obj;
  }
}

VpiHandle VpiContext::AllocObject() {
  auto* obj = new VpiObject();
  all_objects_.push_back(obj);
  return obj;
}

int VpiAllocSchemeFor(VpiAllocKind kind) {
  switch (kind) {
    case VpiAllocKind::kFrameOrThread:
      return kVpiAutomaticScheme;
    case VpiAllocKind::kDynamic:
      return kVpiDynamicScheme;
    default:
      return kVpiOtherScheme;
  }
}

static std::vector<const VpiTypeDeclEntry*> FilterDeclaredUserEntries(
    const std::vector<VpiTypeDeclEntry>& entries) {
  std::vector<const VpiTypeDeclEntry*> visible;
  for (const auto& entry : entries) {
    if (entry.user_defined && entry.declared_in_instance) {
      visible.push_back(&entry);
    }
  }
  return visible;
}

std::vector<const VpiTypeDeclEntry*> VpiInstanceTypedefs(
    const std::vector<VpiTypeDeclEntry>& entries) {
  return FilterDeclaredUserEntries(entries);
}

std::vector<const VpiTypeDeclEntry*> VpiInstanceNetTypedefs(
    const std::vector<VpiTypeDeclEntry>& entries) {
  return FilterDeclaredUserEntries(entries);
}

bool VpiIsInstanceType(int type) {
  return type == kVpiModule || type == vpiPackage || type == vpiInterface ||
         type == vpiProgram;
}

void VpiCollectInstanceAssertions(VpiHandle scope, VpiHandle iter) {
  for (VpiObject* child : scope->children) {
    if (VpiIsAssertionType(child->type)) iter->children.push_back(child);
    if (VpiIsInstanceType(child->type)) continue;
    VpiCollectInstanceAssertions(child, iter);
  }
}

VpiHandle VpiInstanceOf(VpiHandle obj) {
  if (!obj) return nullptr;
  for (VpiObject* scope = obj->parent; scope != nullptr;
       scope = scope->parent) {
    if (VpiIsInstanceType(scope->type)) return scope;
  }
  return nullptr;
}

VpiHandle VpiScopeNamedClockingBlock(VpiHandle scope, bool global) {
  for (auto* child : scope->children) {
    if (child->type != vpiClockingBlock) continue;
    if (global ? child->global_clocking : child->default_clocking) return child;
  }
  return nullptr;
}

VpiHandle VpiScopeDefaultDisableIff(VpiHandle scope) {
  return scope->disable_condition;
}

VpiHandle VpiInstanceArrayOf(VpiHandle element, int type) {
  if (!element->array_member) return nullptr;
  for (VpiObject* array : element->parent->children) {
    bool kind = VpiIsInstanceArrayType(array->type);
    if (type == vpiModuleArray) kind = array->type == vpiModuleArray;
    if (type == vpiPrimitiveArray) kind = VpiIsPrimitiveArrayType(array->type);
    if (kind &&
        std::ranges::find(array->children, element) != array->children.end()) {
      return array;
    }
  }
  return nullptr;
}

namespace {

VpiHandle InstanceArrayElementAt(const VpiObject& array,
                                 std::span<const int> indices) {
  for (VpiObject* child : array.children) {
    if (child->array_member &&
        std::ranges::equal(child->instance_facts.array_indices, indices)) {
      return child;
    }
  }
  return nullptr;
}

}  // namespace

VpiHandle VpiSubobjectByIndices(VpiHandle parent,
                                std::span<const int> indices) {
  if (VpiIsInstanceArrayType(parent->type)) {
    return InstanceArrayElementAt(*parent, indices);
  }
  VpiHandle current = parent;
  for (const int kIndex : indices) {
    VpiHandle next = nullptr;
    for (auto* child : current->children) {
      if (VpiIndexSelects(*current, *child, kIndex)) {
        next = child;
        break;
      }
    }
    if (!next) return nullptr;
    current = next;
  }
  return current;
}

VpiHandle VpiModuleOf(VpiHandle obj) {
  if (!obj) return nullptr;
  for (VpiObject* scope = obj->parent; scope != nullptr;
       scope = scope->parent) {
    if (scope->type == kVpiModule) return scope;
  }
  return nullptr;
}

int VpiMemoryIterationItemType() { return vpiRegArray; }

std::string VpiCompilationUnitFullName(std::string_view object_path) {
  return "$unit::" + std::string(object_path);
}

std::string VpiPackageFullName(std::string_view package_name) {
  return std::string(package_name) + "::";
}

std::string VpiPackageMemberFullName(std::string_view package_name,
                                     std::string_view member_path) {
  return std::string(package_name) + "::" + std::string(member_path);
}

std::string_view VpiNameSeparator(bool package_or_class_defn_boundary) {
  return package_or_class_defn_boundary ? "::" : ".";
}

bool VpiHandleByNameAccessible(const VpiObject& obj) {
  return !obj.imported && !obj.in_compilation_unit;
}

int VpiSmallestTimePrecision(const std::vector<int>& precisions) {
  if (precisions.empty()) return 0;
  int smallest = precisions.front();
  for (int precision : precisions) {
    if (precision < smallest) smallest = precision;
  }
  return smallest;
}

static std::vector<const UdpDecl*> UnitUdpDefinitions(
    const RtlirDesign& design) {
  std::vector<const UdpDecl*> decls;
  if (design.compilation_unit == nullptr) return decls;
  for (const UdpDecl* decl : design.compilation_unit->udps) {
    if (!decl->is_extern) decls.push_back(decl);
  }
  return decls;
}

std::vector<const UdpDecl*> VpiDesignUdpDecls(const RtlirDesign* design) {
  if (design == nullptr) return {};
  std::vector<const UdpDecl*> decls = UnitUdpDefinitions(*design);

  std::vector<const RtlirModule*> work(design->top_modules.begin(),
                                       design->top_modules.end());
  while (!work.empty()) {
    const RtlirModule* mod = work.back();
    work.pop_back();
    if (mod == nullptr) continue;
    for (const auto& child : mod->children) work.push_back(child.resolved);
    for (const RtlirUdpInst& inst : mod->udp_insts) {
      if (inst.decl == nullptr) continue;
      if (std::find(decls.begin(), decls.end(), inst.decl) == decls.end()) {
        decls.push_back(inst.decl);
      }
    }
  }
  return decls;
}

void VpiFillUdpDefnObject(VpiObject* obj, const UdpDecl& decl,
                          std::deque<std::string>& names) {
  obj->type = vpiUdpDefn;
  names.emplace_back(decl.name);
  obj->name = names.back();
  obj->def_name = std::string(decl.name);
  obj->size = static_cast<int>(decl.input_names.size());
  obj->prim_type = decl.is_sequential ? vpiSeqPrim : vpiCombPrim;
}

static std::string DecompiledUdpRow(const UdpTableRow& row) {
  std::string text;
  for (std::size_t i = 0; i < row.inputs.size(); ++i) {
    if (i > 0) text += ' ';
    if (row.inputs[i] != '\x01') {
      text += row.inputs[i];
      continue;
    }
    text += '(';
    text += row.paren_edges[i].first;
    text += row.paren_edges[i].second;
    text += ')';
  }
  if (row.current_state != 0) {
    text += " : ";
    text += row.current_state;
  }
  text += " : ";
  text += row.output;
  return text;
}

VpiObject* VpiUdpInitialStatement(const UdpDecl& decl, VpiObject* initial,
                                  const std::function<VpiObject*()>& alloc,
                                  std::deque<std::string>& names,
                                  Arena& arena) {
  VpiObject* assign = alloc();
  assign->type = vpiAssignment;
  assign->blocking = true;
  assign->parent = initial;
  VpiObject* lhs = alloc();
  lhs->type = kVpiReg;
  names.emplace_back(decl.output_name);
  lhs->name = names.back();
  lhs->size = 1;
  lhs->parent = assign;
  VpiObject* rhs = alloc();
  rhs->type = vpiConstant;
  rhs->const_type = vpiBinaryConst;
  rhs->size = 1;
  rhs->parent = assign;
  auto* bit = arena.Create<Variable>();
  const char kBit = decl.initial_value;
  bit->value = kBit == '0' || kBit == '1'
                   ? MakeLogic4VecVal(arena, 1, kBit == '1' ? 1 : 0)
                   : MakeAllX(arena, 1);
  rhs->var = bit;
  assign->lhs = lhs;
  assign->rhs = rhs;
  return assign;
}

void VpiFillUdpTableEntryObject(VpiObject* obj, const UdpTableRow& row,
                                VpiObject* defn, Arena& arena) {
  obj->type = vpiTableEntry;
  obj->size = static_cast<int>(row.inputs.size()) +
              (row.current_state != 0 ? 1 : 0) + 1;
  auto* text = arena.Create<Variable>();
  text->value = StringToLogic4Vec(arena, DecompiledUdpRow(row));
  obj->var = text;
  obj->parent = defn;
  defn->children.push_back(obj);
}

static std::string_view SpecifyEntryScope(std::string_view inst_prefix,
                                          std::string_view first_top) {
  if (inst_prefix.empty()) return first_top;
  inst_prefix.remove_suffix(1);
  return inst_prefix;
}

static VpiHandle ModulePathOutputNet(VpiHandle module,
                                     std::string_view dst_port) {
  for (VpiHandle child : module->children) {
    if (VpiIsNetsType(child->type) && child->name == dst_port) return child;
  }
  return nullptr;
}

static int VpiEventEdgeOf(SpecifyEdge edge) {
  switch (edge) {
    case SpecifyEdge::kPosedge:
      return vpiPosedge;
    case SpecifyEdge::kNegedge:
      return vpiNegedge;
    case SpecifyEdge::kEdge:
      return vpiAnyEdge;
    default:
      return vpiNoEdge;
  }
}

static const Expr* TerminalExpression(const SpecifyTerminal& terminal,
                                      Arena& arena) {
  auto* signal = arena.Create<Expr>();
  signal->kind = ExprKind::kIdentifier;
  signal->text = terminal.name;
  if (!terminal.interface_name.empty()) {
    auto* port = arena.Create<Expr>();
    port->kind = ExprKind::kIdentifier;
    port->text = terminal.interface_name;
    auto* member = arena.Create<Expr>();
    member->kind = ExprKind::kMemberAccess;
    member->lhs = port;
    member->rhs = signal;
    signal = member;
  }
  if (terminal.range_kind == SpecifyRangeKind::kNone) return signal;
  auto* select = arena.Create<Expr>();
  select->kind = ExprKind::kSelect;
  select->base = signal;
  select->index = terminal.range_left;
  if (terminal.range_kind != SpecifyRangeKind::kBitSelect) {
    select->index_end = terminal.range_right;
  }
  select->is_part_select_plus =
      terminal.range_kind == SpecifyRangeKind::kPlusIndexed;
  select->is_part_select_minus =
      terminal.range_kind == SpecifyRangeKind::kMinusIndexed;
  return select;
}

using WrittenExpression = std::function<VpiObject*(const Expr*)>;

static WrittenExpression ExpressionsIn(std::string_view inst_prefix,
                                       const VpiObjectMap& objects,
                                       SimContext& ctx,
                                       const VpiAttachBuild& build) {
  return [prefix = std::string(SpecifyEntryScope(inst_prefix, "")), &objects,
          &ctx, &build](const Expr* expr) {
    return VpiInstanceExpression(expr, objects, prefix, ctx, build);
  };
}

static VpiObject* AddPathTerm(VpiObject* path, int direction, int edge,
                              VpiObject* expr, const VpiAttachBuild& build) {
  VpiObject* term = build.alloc();
  term->type = vpiPathTerm;
  term->direction = direction;
  term->edge = edge;
  term->term_expr = expr;
  term->parent = path;
  path->children.push_back(term);
  return term;
}

static int VpiPolarityOf(SpecifyPolarity polarity) {
  switch (polarity) {
    case SpecifyPolarity::kPositive:
      return vpiPositive;
    case SpecifyPolarity::kNegative:
      return vpiNegative;
    default:
      return vpiUnknown;
  }
}

static void FillModPath(VpiObject* obj, const PathDelay& path,
                        const WrittenExpression& expr,
                        const VpiAttachBuild& build) {
  const SpecifyPathDecl& decl = *path.decl;
  obj->path_type =
      decl.path_kind == SpecifyPathKind::kFull ? vpiPathFull : vpiPathParallel;
  obj->polarity = VpiPolarityOf(decl.polarity);
  obj->data_polarity = VpiPolarityOf(decl.dst_polarity);
  obj->mod_path_has_if_none = decl.is_ifnone;
  obj->written_condition = expr(decl.condition);
  if (path.src_index < decl.src_ports.size()) {
    AddPathTerm(
        obj, vpiInput, VpiEventEdgeOf(decl.edge),
        expr(TerminalExpression(decl.src_ports[path.src_index], build.arena)),
        build);
  }
  if (path.dst_index < decl.dst_ports.size()) {
    AddPathTerm(
        obj, vpiOutput, vpiNoEdge,
        expr(TerminalExpression(decl.dst_ports[path.dst_index], build.arena)),
        build);
  }
  if (decl.data_source != nullptr) {
    AddPathTerm(obj, vpiInput, vpiNoEdge, expr(decl.data_source), build)
        ->data_path_term = true;
  }
}

void VpiContext::AttachModulePathDelays(SimContext& sim_ctx) {
  SpecifyManager* specify = sim_ctx.GetSpecifyManager();
  if (specify == nullptr) return;
  const VpiAttachBuild kBuild{[this] { return AllocObject(); },
                              VpiPoolKeeper(name_pool_), sim_ctx.GetArena()};

  for (const PathDelay& path : specify->GetPathDelays()) {
    std::string_view scope =
        SpecifyEntryScope(path.inst_prefix, sim_ctx.FirstTopModule());
    if (scope.empty()) continue;
    VpiHandle module = DesignObjectForFlatName(scope);

    auto* obj = AllocObject();
    obj->type = vpiModPath;
    obj->parent = module;
    run_entry_index_[obj] =
        static_cast<std::size_t>(&path - specify->GetPathDelays().data());
    module->children.push_back(obj);
    obj->delay_expr =
        VpiSourceDelayExpression(path.source_delays, path.inst_prefix, sim_ctx,
                                 [this] { return AllocObject(); });
    VpiRecordWrittenLocation(obj, path.loc, sim_ctx);
    obj->delays.reserve(path.delay_count);
    const bool kWritten = path.source_delays.size() == path.delay_count;
    InstancePrefixOverride in_instance(sim_ctx.InstancePrefixOverride(),
                                       path.inst_prefix);
    for (uint8_t i = 0; i < path.delay_count; ++i) {
      VpiDelayInfo info;
      if (kWritten && path.source_delays[i] != nullptr) {
        info = VpiWrittenDelay(path.source_delays[i], sim_ctx);
      } else {
        info.min_delay = info.typ_delay = info.max_delay =
            static_cast<double>(path.delays[i]);
      }
      info.delay = static_cast<double>(path.delays[i]);
      info.reject = static_cast<double>(path.reject_limit[i]);
      info.min_reject = info.reject;
      info.typ_reject = info.reject;
      info.max_reject = info.reject;
      info.error = static_cast<double>(path.error_limit[i]);
      info.min_error = info.error;
      info.typ_error = info.error;
      info.max_error = info.error;
      obj->delays.push_back(info);
    }
    VpiPlaceDelayDevice(obj, ModulePathOutputNet(module, path.dst_port), module,
                        vpiModPathDelay, [this] { return AllocObject(); });
    if (path.decl != nullptr) {
      FillModPath(obj, path,
                  ExpressionsIn(path.inst_prefix, object_map_, sim_ctx, kBuild),
                  kBuild);
    }
  }
}

static int VpiTchkTypeOf(TimingCheckKind kind) {
  switch (kind) {
    case TimingCheckKind::kSetup:
      return vpiSetup;
    case TimingCheckKind::kHold:
      return vpiHold;
    case TimingCheckKind::kSetuphold:
      return vpiSetupHold;
    case TimingCheckKind::kRecovery:
      return vpiRecovery;
    case TimingCheckKind::kRemoval:
      return vpiRemoval;
    case TimingCheckKind::kRecrem:
      return vpiRecrem;
    case TimingCheckKind::kWidth:
      return vpiWidth;
    case TimingCheckKind::kPeriod:
      return vpiPeriod;
    case TimingCheckKind::kSkew:
      return vpiSkew;
    case TimingCheckKind::kNochange:
      return vpiNoChange;
    case TimingCheckKind::kTimeskew:
      return vpiTimeskew;
    default:
      return vpiFullskew;
  }
}

struct VpiEdgeTransition {
  char from;
  char to;
  int bit;
};

constexpr std::array<VpiEdgeTransition, 6> kVpiEdgeTransitions = {{
    {'0', '1', vpiEdge01},
    {'1', '0', vpiEdge10},
    {'0', 'x', vpiEdge0x},
    {'x', '1', vpiEdgex1},
    {'1', 'x', vpiEdge1x},
    {'x', '0', vpiEdgex0},
}};

static int VpiTchkEventEdgeOf(
    SpecifyEdge edge, const std::vector<std::pair<char, char>>& descriptors) {
  if (descriptors.empty()) return VpiEventEdgeOf(edge);
  int mask = vpiNoEdge;
  for (const auto& [from, to] : descriptors) {
    for (const VpiEdgeTransition& transition : kVpiEdgeTransitions) {
      if (transition.from == from && transition.to == to)
        mask |= transition.bit;
    }
  }
  return mask;
}

static VpiObject* MakeTchkTerm(VpiObject* term, std::string_view signal,
                               int edge, VpiObject* tchk,
                               std::deque<std::string>& names) {
  term->type = vpiTchkTerm;
  names.emplace_back(signal);
  term->name = names.back();
  term->edge = edge;
  term->parent = tchk;
  tchk->children.push_back(term);
  return term;
}

static int LimitCountOf(TimingCheckKind kind) {
  if (kind == TimingCheckKind::kNochange) return 0;
  return kind == TimingCheckKind::kSetuphold ||
                 kind == TimingCheckKind::kRecrem ||
                 kind == TimingCheckKind::kFullskew
             ? 2
             : 1;
}

static void AddTchkLimit(VpiObject* tchk, uint64_t ticks) {
  VpiDelayInfo limit;
  limit.delay = static_cast<double>(ticks);
  limit.min_delay = limit.delay;
  limit.typ_delay = limit.delay;
  limit.max_delay = limit.delay;
  tchk->delays.push_back(limit);
}

static const Expr* DelayedSignalExpression(std::string_view name, Expr* index,
                                           Arena& arena) {
  if (name.empty()) return nullptr;
  SpecifyTerminal terminal;
  terminal.name = name;
  terminal.range_left = index;
  if (index != nullptr) terminal.range_kind = SpecifyRangeKind::kBitSelect;
  return TerminalExpression(terminal, arena);
}

static void FillTchkTerm(VpiObject* term, const SpecifyTerminal& terminal,
                         const Expr* condition, const WrittenExpression& expr,
                         Arena& arena) {
  if (term == nullptr) return;
  term->term_expr = expr(TerminalExpression(terminal, arena));
  term->written_condition = expr(condition);
}

static void FillTchkArguments(VpiObject* tchk, const TimingCheckDecl& decl,
                              const WrittenExpression& expr, Arena& arena) {
  VpiObject* first = tchk->tchk_ref_term;
  VpiObject* second = tchk->tchk_data_term;
  FillTchkTerm(first, decl.ref_terminal, decl.ref_condition, expr, arena);
  FillTchkTerm(second, decl.data_terminal, decl.data_condition, expr, arena);
  if (decl.check_kind == TimingCheckKind::kSetup) std::swap(first, second);
  std::vector<VpiObject*> arguments = {first, second};
  for (const Expr* limit : decl.limits) arguments.push_back(expr(limit));
  arguments.push_back(tchk->tchk_notifier);
  const std::vector<const Expr*> kTrailing = {
      decl.timestamp_cond,
      decl.timecheck_cond,
      DelayedSignalExpression(decl.delayed_ref, decl.delayed_ref_expr, arena),
      DelayedSignalExpression(decl.delayed_data, decl.delayed_data_expr, arena),
      decl.event_based_flag,
      decl.remain_active_flag};
  for (const Expr* trailing : kTrailing) arguments.push_back(expr(trailing));
  std::erase(arguments, nullptr);
  tchk->tchk_arguments = std::move(arguments);
}

void VpiContext::AttachTimingChecks(SimContext& sim_ctx) {
  SpecifyManager* specify = sim_ctx.GetSpecifyManager();
  if (specify == nullptr) return;
  const VpiAttachBuild kBuild{[this] { return AllocObject(); },
                              VpiPoolKeeper(name_pool_), sim_ctx.GetArena()};

  for (const TimingCheckEntry& check : specify->GetTimingChecks()) {
    std::string_view scope =
        SpecifyEntryScope(check.inst_prefix, sim_ctx.FirstTopModule());
    if (scope.empty()) continue;
    VpiHandle module = DesignObjectForFlatName(scope);

    auto* obj = AllocObject();
    obj->type = vpiTchk;
    obj->tchk_type = VpiTchkTypeOf(check.kind);
    obj->parent = module;
    run_entry_index_[obj] =
        static_cast<std::size_t>(&check - specify->GetTimingChecks().data());
    module->children.push_back(obj);
    obj->delay_expr =
        VpiSourceDelayExpression(check.source_limits, check.inst_prefix,
                                 sim_ctx, [this] { return AllocObject(); });
    VpiRecordWrittenLocation(obj, check.loc, sim_ctx);

    const int kLimits = LimitCountOf(check.kind);
    if (kLimits > 0) AddTchkLimit(obj, check.limit);
    if (kLimits > 1) AddTchkLimit(obj, check.limit2);

    obj->tchk_ref_term = MakeTchkTerm(
        AllocObject(), check.ref_signal,
        VpiTchkEventEdgeOf(check.ref_edge, check.ref_edge_descriptors), obj,
        name_pool_);
    if (!check.data_signal.empty()) {
      obj->tchk_data_term = MakeTchkTerm(
          AllocObject(), check.data_signal,
          VpiTchkEventEdgeOf(check.data_edge, check.data_edge_descriptors), obj,
          name_pool_);
    }

    if (!check.notifier.empty()) {
      obj->tchk_notifier = DesignObjectForFlatName(
          std::string(check.inst_prefix) + std::string(check.notifier));
    }

    if (check.decl == nullptr) continue;
    FillTchkArguments(
        obj, *check.decl,
        ExpressionsIn(check.inst_prefix, object_map_, sim_ctx, kBuild),
        sim_ctx.GetArena());
  }
}

void VpiContext::NoteTimingViolation(const TimingCheckEntry& check) {
  if (sim_ctx_ == nullptr || !HasCallbackFor(callbacks_, cbTchkViolation)) {
    return;
  }
  const SpecifyManager* specify = sim_ctx_->GetSpecifyManager();
  if (specify == nullptr) return;
  const auto kIndex =
      static_cast<std::size_t>(&check - specify->GetTimingChecks().data());
  for (const auto& [obj, index] : run_entry_index_) {
    if (obj->type == vpiTchk && index == kIndex) {
      DispatchCallbacks(cbTchkViolation, const_cast<VpiObject*>(obj));
      return;
    }
  }
}

}  // namespace delta
