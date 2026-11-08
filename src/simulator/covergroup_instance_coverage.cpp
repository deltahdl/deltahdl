#include <array>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"
#include "simulator/covergroup_instance.h"
#include "simulator/covergroup_instance_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

namespace {

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

struct CovergroupType {
  const CovergroupDecl* decl = nullptr;
  const ClassTypeInfo* declaring_class = nullptr;
};

CovergroupType TypeOf(const CovergroupInstance& inst) {
  return {inst.decl, inst.declaring_class};
}

std::deque<CoverGroup> TypeRecords(const CovergroupType& type, bool merge,
                                   SimContext& ctx) {
  std::deque<CoverGroup> records;
  for (const CoverGroup* group :
       ctx.Covergroups().InstancesOf(type.decl, type.declaring_class)) {
    records.push_back(*group);
  }
  const CoverGroup* cumulative =
      ctx.CoverageData().LoadedCoverageOf(type.decl->name);
  if (cumulative == nullptr) return records;
  if (merge || records.empty()) {
    records.push_front(*cumulative);
    return records;
  }
  for (CoverGroup& group : records) {
    CoverageDB::AddCumulativeCounts(group, *cumulative);
  }
  return records;
}

bool MergesInstances(const CovergroupInstance& inst) {
  return inst.group->type_option.merge_instances;
}

double TypeCoverage(const CovergroupType& type, bool merge, SimContext& ctx,
                    int32_t& covered, int32_t& total) {
  std::deque<CoverGroup> records = TypeRecords(type, merge, ctx);
  std::vector<const CoverGroup*> instances;
  instances.reserve(records.size());
  covered = 0;
  total = 0;
  for (const CoverGroup& group : records) {
    int32_t n = 0;
    int32_t t = 0;
    CoverageDB::GetCoverage(&group, n, t);
    covered += n;
    total += t;
    instances.push_back(&group);
  }
  return CoverageDB::ComputeTypeCoverage(instances, merge);
}

std::vector<const CoverPoint*> PointsNamed(
    const std::deque<CoverGroup>& records, const std::string& name) {
  std::vector<const CoverPoint*> found;
  for (const CoverGroup& group : records) {
    for (const CoverPoint& cp : group.coverpoints) {
      if (cp.name == name) found.push_back(&cp);
    }
  }
  return found;
}

std::vector<const CrossCover*> CrossesNamed(
    const std::deque<CoverGroup>& records, const std::string& name) {
  std::vector<const CrossCover*> found;
  for (const CoverGroup& group : records) {
    for (const CrossCover& cross : group.crosses) {
      if (cross.name == name) found.push_back(&cross);
    }
  }
  return found;
}

struct CoverageReading {
  double coverage = 0.0;
  int32_t covered = 0;
  int32_t total = 0;
};

CoverageReading ItemTypeReading(const CovergroupType& type,
                                const std::string& name, bool merge,
                                SimContext& ctx) {
  CoverageReading r;
  std::deque<CoverGroup> records = TypeRecords(type, merge, ctx);
  std::vector<const CoverPoint*> points = PointsNamed(records, name);
  for (const CoverPoint* cp : points) {
    int32_t n = 0;
    int32_t t = 0;
    CoverageDB::GetPointCoverage(cp, n, t);
    r.covered += n;
    r.total += t;
  }
  if (!points.empty()) {
    r.coverage = CoverageDB::ComputePointTypeCoverage(points, merge);
    return r;
  }
  std::vector<const CrossCover*> crosses = CrossesNamed(records, name);
  for (const CrossCover* cross : crosses) {
    int32_t n = 0;
    int32_t t = 0;
    CoverageDB::GetCrossCoverage(cross, n, t);
    r.covered += n;
    r.total += t;
  }
  r.coverage = CoverageDB::ComputeCrossTypeCoverage(crosses, merge);
  return r;
}

const Expr* CoverageCallType(const Expr* type_expr, std::string& item) {
  if (type_expr->kind == ExprKind::kMemberAccess &&
      type_expr->is_scope_resolution && type_expr->lhs != nullptr &&
      type_expr->rhs != nullptr &&
      type_expr->rhs->kind == ExprKind::kIdentifier) {
    item = std::string(type_expr->rhs->text);
    return type_expr->lhs;
  }
  return type_expr;
}

const CovergroupDecl* CovergroupTypeNamed(const Expr* scope, SimContext& ctx,
                                          std::string& item) {
  const ModuleItem* found =
      ctx.FindLetDecl(CoverageCallType(scope, item)->text);
  if (found == nullptr || found->kind != ModuleItemKind::kCovergroupDecl) {
    return nullptr;
  }
  return found->covergroup;
}

}  // namespace

const CovergroupDecl* TypeOptionOwner(const Expr* access, SimContext& ctx,
                                      std::string& item) {
  if (!access->is_scope_resolution || access->rhs == nullptr ||
      access->rhs->text != "type_option" || access->lhs == nullptr) {
    return nullptr;
  }
  return CovergroupTypeNamed(access->lhs, ctx, item);
}

Logic4Vec ReportCoverage(const CovergroupTarget& target, const Expr* call,
                         bool instance, SimContext& ctx, Arena& arena) {
  int32_t covered = 0;
  int32_t total = 0;
  double coverage = 0.0;
  const CovergroupInstance& inst = *target.inst;
  bool merge = MergesInstances(inst);
  if ((target.point != nullptr || target.cross != nullptr) && !instance) {
    CoverageReading r = ItemTypeReading(
        TypeOf(inst),
        target.point != nullptr ? target.point->point->name
                                : inst.group->crosses[target.cross->index].name,
        merge, ctx);
    coverage = r.coverage;
    covered = r.covered;
    total = r.total;
  } else if (target.point != nullptr) {
    coverage =
        CoverageDB::GetPointCoverage(target.point->point, covered, total);
  } else if (target.cross != nullptr) {
    coverage = CoverageDB::GetCrossCoverage(
        &inst.group->crosses[target.cross->index], covered, total);
  } else if (instance && (!merge || inst.group->options.get_inst_coverage)) {
    coverage = CoverageDB::GetInstCoverage(inst.group, covered, total);
  } else {
    coverage = TypeCoverage(TypeOf(inst), merge, ctx, covered, total);
  }
  WriteCounts(call, covered, total, ctx, arena);
  return MakeRealVec(arena, coverage, 64);
}

bool TryEvalTypeCoverageCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out) {
  const Expr* access = expr->lhs;
  if (access->rhs->text != "get_coverage") return false;
  std::string item_name;
  const CovergroupDecl* decl = CovergroupTypeNamed(access->lhs, ctx, item_name);
  if (decl == nullptr) return false;
  const CovergroupType kType{decl, nullptr};
  std::vector<const CoverGroup*> instances =
      ctx.Covergroups().InstancesOf(decl, nullptr);
  bool merge = !instances.empty() && instances[0]->type_option.merge_instances;
  CoverageReading r;
  if (item_name.empty()) {
    r.coverage = TypeCoverage(kType, merge, ctx, r.covered, r.total);
  } else {
    r = ItemTypeReading(kType, item_name, merge, ctx);
  }
  WriteCounts(expr, r.covered, r.total, ctx, arena);
  out = MakeRealVec(arena, r.coverage, 64);
  return true;
}

}  // namespace delta
