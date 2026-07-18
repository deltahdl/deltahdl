#include <algorithm>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {
namespace {

// A rand/randc variable discovered on the randomized object, paired with the
// class level that declares it (for the scoped "Class::name" property alias)
// and the solver variable being built for it.
struct RandInfo {
  std::string name;
  const ClassTypeInfo* level = nullptr;
  // 18.4.2: a static randc shares its cyclic permutation across every instance
  // of the declaring class, so its history is stored on the (shared) class type
  // rather than on the object. Track the static-ness of the source member here.
  bool is_static = false;
  RandVariable var;

  // 18.5.8: in a joint (global-constraint) solve the same variable name can
  // appear on several objects, so 'name' carries a path-qualified name unique
  // across the whole active random object tree while 'member' keeps the plain
  // property name and 'owner' names the object the value is written back to.
  // For an ordinary single-object solve owner stays null and member stays
  // empty, and the single object's own name/level are used, so nothing changes
  // there.
  std::string member;
  ClassObject* owner = nullptr;
};

// State threaded through the randomize() build helpers; bundled to keep helper
// parameter lists small.
struct RandomizeCtx {
  ClassObject* obj;
  SimContext& ctx;
  Arena& arena;
  // 18.5.13: stable storage for the inner relation of each soft constraint. A
  // kSoft ConstraintExpr points to its inner relation through a raw pointer, so
  // the inner must outlive the solve; owning it on the heap here keeps that
  // address stable even as the solver copies the block holding the kSoft.
  std::vector<std::unique_ptr<ConstraintExpr>> soft_inners = {};
};

RandInfo* FindRand(std::vector<RandInfo>& rands, std::string_view name) {
  for (auto& ri : rands) {
    if (std::string_view(ri.name) == name) return &ri;
  }
  return nullptr;
}

// 18.3: fold an enum's named-constant list into the concrete integer values it
// defines, applying the same source-order auto-increment rule the type
// declaration uses: a member with an explicit value resets the running counter,
// and each subsequent unspecified member is one greater than the last.
void FoldEnumMemberValues(const std::vector<EnumMember>& members,
                          std::vector<int64_t>& out) {
  int64_t next = 0;
  for (const auto& em : members) {
    if (em.value != nullptr) next = static_cast<int64_t>(em.value->int_val);
    out.push_back(next);
    ++next;
  }
}

// 18.3: for an active random variable of enum type, the solver shall select a
// value only from the set of named constants of that enum, and shall never
// assign a value that lies outside that set even when the value would cast
// cleanly to the enumerated type. Resolve the member's enum type to its named
// constants and record them as the solver domain; a non-enum member is left
// unrestricted. The enum type may be written inline on the declaration
// (`rand enum {...} x;`) or named through a typedef declared on the class or an
// ancestor (`rand col_e x;` as in the 18.3 MyBus example's atype), and a
// package- or module-scope enum typedef is found through the enum registry, so
// all three forms are resolved here.
void PopulateEnumDomain(const ClassMember* m, const ClassTypeInfo* level,
                        SimContext& ctx, RandVariable& var) {
  const DataType& dt = m->data_type;
  if (dt.kind == DataTypeKind::kEnum) {
    FoldEnumMemberValues(dt.enum_members, var.enum_values);
    return;
  }
  if (dt.kind != DataTypeKind::kNamed) return;
  for (const ClassTypeInfo* lvl = level; lvl != nullptr; lvl = lvl->parent) {
    if (lvl->decl == nullptr) continue;
    for (const ClassMember* tm : lvl->decl->members) {
      if (tm->kind == ClassMemberKind::kTypedef &&
          tm->typedef_item != nullptr &&
          tm->typedef_item->typedef_type.kind == DataTypeKind::kEnum &&
          tm->typedef_item->name == dt.type_name) {
        FoldEnumMemberValues(tm->typedef_item->typedef_type.enum_members,
                             var.enum_values);
        return;
      }
    }
  }
  if (const EnumTypeInfo* info = ctx.FindEnumType(dt.type_name)) {
    for (const auto& em : info->members)
      var.enum_values.push_back(static_cast<int64_t>(em.value));
  }
}

// 18.4: build a solver variable for one rand/randc data member. The default
// integral domain is later tightened by the relational constraints.
void AddRandMember(const ClassMember* m, const ClassTypeInfo* level,
                   SimContext& ctx, std::vector<RandInfo>& out) {
  RandInfo info;
  info.name = std::string(m->name);
  info.level = level;
  info.is_static = m->is_static;
  info.var.name = info.name;
  info.var.qualifier =
      m->is_randc ? RandQualifier::kRandc : RandQualifier::kRand;
  uint32_t width = EvalTypeWidth(m->data_type);
  info.var.width = width == 0 ? 32 : width;
  // 18.3: confine an enum-typed random variable to its named-constant set.
  PopulateEnumDomain(m, level, ctx, info.var);
  // 18.4.2: a randc variable's cyclic permutation ranges over every value its
  // declared width admits (0 .. 2**w-1). The generic solver domain defaults to
  // a fixed 16-bit span; leaving a randc on that default would let the cyclic
  // draw range over more values than the member can hold and then truncate on
  // write-back, destroying the no-repeat property over the real declared range.
  // Bind the domain to the declared width here so the permutation matches the
  // range; later constraint folding narrows it further. A plain rand keeps the
  // generic default -- a uniform draw truncated to the member width is still
  // uniform -- so only the cyclic form needs the exact bound.
  if (info.var.qualifier == RandQualifier::kRandc) {
    uint32_t w = info.var.width;
    info.var.min_val = 0;
    info.var.max_val =
        w >= 63 ? INT64_MAX : ((static_cast<int64_t>(1) << w) - 1);
  }
  out.push_back(std::move(info));
}

// 18.4: a rand class-handle member names an object; randomize() solves that
// object's own random members and shall never modify the handle itself. The
// handle is therefore not built as a solver variable — doing so would draw an
// integer and overwrite the handle on writeback. (The recursive solve of the
// referenced object is a separate concern; the head-level obligation observed
// here is simply that the handle value is left unchanged.)
bool IsClassHandleMember(const ClassMember* m, SimContext& ctx) {
  return m->data_type.kind == DataTypeKind::kNamed &&
         ctx.FindClassType(m->data_type.type_name) != nullptr;
}

// 18.4: gather every rand/randc data member visible on the object, walking the
// inheritance chain so inherited random variables are included. Class-handle
// members are skipped so the handle they hold is never overwritten.
void CollectRandVariables(const ClassTypeInfo* type, SimContext& ctx,
                          std::vector<RandInfo>& out) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kProperty &&
          (m->is_rand || m->is_randc) && !IsClassHandleMember(m, ctx))
        AddRandMember(m, lvl, ctx, out);
    }
  }
}

// 18.5: the comparison operators a relation can fold into a domain bound or a
// typed solver constraint. Returns the solver kind for the var-on-left form;
// callers mirror the operator for the var-on-right form before calling.
bool ComparisonKind(TokenKind op, ConstraintKind& out) {
  switch (op) {
    case TokenKind::kGtEq:
      out = ConstraintKind::kGreaterEqual;
      return true;
    case TokenKind::kLtEq:
      out = ConstraintKind::kLessEqual;
      return true;
    case TokenKind::kGt:
      out = ConstraintKind::kGreaterThan;
      return true;
    case TokenKind::kLt:
      out = ConstraintKind::kLessThan;
      return true;
    case TokenKind::kEqEq:
      out = ConstraintKind::kEqual;
      return true;
    case TokenKind::kBangEq:
      out = ConstraintKind::kNotEqual;
      return true;
    default:
      return false;
  }
}

TokenKind MirrorComparison(TokenKind op) {
  switch (op) {
    case TokenKind::kGtEq:
      return TokenKind::kLtEq;
    case TokenKind::kLtEq:
      return TokenKind::kGtEq;
    case TokenKind::kGt:
      return TokenKind::kLt;
    case TokenKind::kLt:
      return TokenKind::kGt;
    default:
      return op;  // == and != are symmetric
  }
}

// 18.5/18.5.13: tighten a relation 'var <op> constant' into the variable's draw
// domain so the 500-attempt generate-and-test solver reliably hits it.
void FoldBound(RandInfo& ri, ConstraintKind kind, int64_t c) {
  switch (kind) {
    case ConstraintKind::kGreaterEqual:
      ri.var.min_val = std::max(ri.var.min_val, c);
      break;
    case ConstraintKind::kGreaterThan:
      ri.var.min_val = std::max(ri.var.min_val, c + 1);
      break;
    case ConstraintKind::kLessEqual:
      ri.var.max_val = std::min(ri.var.max_val, c);
      break;
    case ConstraintKind::kLessThan:
      ri.var.max_val = std::min(ri.var.max_val, c - 1);
      break;
    default:
      break;
  }
}

// 18.5: a comparison of a rand variable against a constant. Fills `out` with
// the typed solver constraint, folds the variable's domain, and returns true;
// other relation shapes return false for the kCustom fallback.
bool TryComparisonConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                             RandomizeCtx& rc, ConstraintExpr& out,
                             bool fold = true) {
  if (!rel || rel->kind != ExprKind::kBinary || !rel->lhs || !rel->rhs)
    return false;
  ConstraintKind kind = ConstraintKind::kEqual;
  if (!ComparisonKind(rel->op, kind)) return false;
  const Expr* var_side = nullptr;
  const Expr* const_side = nullptr;
  bool mirror = false;
  if (rel->lhs->kind == ExprKind::kIdentifier &&
      FindRand(rands, rel->lhs->text)) {
    var_side = rel->lhs;
    const_side = rel->rhs;
  } else if (rel->rhs->kind == ExprKind::kIdentifier &&
             FindRand(rands, rel->rhs->text)) {
    var_side = rel->rhs;
    const_side = rel->lhs;
    mirror = true;
  }
  if (!var_side) return false;
  if (mirror) ComparisonKind(MirrorComparison(rel->op), kind);
  auto c =
      static_cast<int64_t>(EvalExpr(const_side, rc.ctx, rc.arena).ToUint64());
  out.kind = kind;
  out.var_name = std::string(var_side->text);
  out.lo = c;
  out.ref_vars.push_back(out.var_name);
  // 18.5.13: a soft relation must not tighten the variable's draw domain. If it
  // did, a discarded soft preference would still constrain the variable,
  // biasing the result and narrowing the values the hard constraints still
  // allow.
  if (fold)
    if (auto* ri = FindRand(rands, var_side->text)) FoldBound(*ri, kind, c);
  return true;
}

// Evaluate a non-foldable relation against candidate values: bind each rand
// variable as a local so the expression reads the trial value.
bool EvalCustomRelation(const Expr* rel, const std::vector<std::string>& names,
                        RandomizeCtx& rc,
                        const std::unordered_map<std::string, int64_t>& vals) {
  rc.ctx.PushScope();
  rc.ctx.PushThis(rc.obj);
  for (const auto& n : names) {
    auto it = vals.find(n);
    int64_t v = it != vals.end() ? it->second : 0;
    rc.ctx.CreateLocalVariable(n, 32)->value =
        MakeLogic4VecVal(rc.arena, 32, static_cast<uint64_t>(v));
  }
  Logic4Vec r = EvalExpr(rel, rc.ctx, rc.arena);
  rc.ctx.PopThis();
  rc.ctx.PopScope();
  return r.IsTruthy();
}

ConstraintExpr MakeCustomConstraint(const Expr* rel,
                                    const std::vector<RandInfo>& rands,
                                    RandomizeCtx& rc) {
  std::vector<std::string> names;
  names.reserve(rands.size());
  for (const auto& ri : rands) names.push_back(ri.name);
  ConstraintExpr ce;
  ce.kind = ConstraintKind::kCustom;
  ce.ref_vars = names;
  ce.eval_fn = [rel, names,
                &rc](const std::unordered_map<std::string, int64_t>& vals) {
    return EvalCustomRelation(rel, names, rc, vals);
  };
  return ce;
}

// 18.5: translate one captured constraint relation into a solver
// ConstraintExpr.
ConstraintExpr TranslateRelation(const Expr* rel, std::vector<RandInfo>& rands,
                                 RandomizeCtx& rc, bool fold = true) {
  ConstraintExpr ce;
  if (TryComparisonConstraint(rel, rands, rc, ce, fold)) return ce;
  return MakeCustomConstraint(rel, rands, rc);
}

// 18.5.3: translate a captured "expression dist { dist_list }" into a kDist
// solver constraint. The distribution names the single variable it weights, so
// the target must be a plain identifier; each item's value/range bounds and its
// weight are constant expressions, folded to integers here. A range keeps its
// per_element flag so the solver spreads a ':=' weight across the range, and an
// item with no explicit weight keeps the DistWeight default weight of 1.
// Returns false for a non-identifier target, leaving the distribution unbuilt.
bool BuildDistConstraint(const ConstraintDistRef& ref, RandomizeCtx& rc,
                         ConstraintExpr& out) {
  if (ref.target == nullptr || ref.target->kind != ExprKind::kIdentifier)
    return false;
  out.kind = ConstraintKind::kDist;
  out.var_name = std::string(ref.target->text);
  for (const auto& item : ref.items) {
    DistWeight w;
    w.is_default = item.is_default;
    w.is_range = item.is_range;
    w.per_element = item.per_element;
    if (item.weight != nullptr)
      w.weight = static_cast<uint32_t>(
          EvalExpr(item.weight, rc.ctx, rc.arena).ToUint64());
    if (item.is_range) {
      w.lo =
          static_cast<int64_t>(EvalExpr(item.lo, rc.ctx, rc.arena).ToUint64());
      w.hi =
          static_cast<int64_t>(EvalExpr(item.hi, rc.ctx, rc.arena).ToUint64());
    } else if (!item.is_default) {
      w.value = static_cast<int64_t>(
          EvalExpr(item.value, rc.ctx, rc.arena).ToUint64());
    }
    out.dist_weights.push_back(w);
  }
  return true;
}

// 18.5.10: locate the constraint block named `name` in the object's class
// hierarchy, walking from the dynamic type up to its base classes so the
// most-derived block of a given name wins (matching CollectConstraintBlocks).
// A block qualified 'static' shares one active/inactive state across every
// instance of its declaring class, so its state lives on the ClassTypeInfo
// rather than the object; this returns that declaring type when the block is
// static, and nullptr otherwise.
static const ClassTypeInfo* StaticConstraintOwner(const ClassObject* obj,
                                                  std::string_view name) {
  for (const auto* lvl = obj ? obj->type : nullptr; lvl != nullptr;
       lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kConstraint && m->name == name)
        return m->is_static ? lvl : nullptr;
    }
  }
  return nullptr;
}

// 18.9: report whether a constraint block is active on this object. Every block
// is active when the object is created, so an absent entry means active.
// 18.5.10: for a static block the state is the class-wide one shared by all
// instances, kept on the declaring type rather than on this object.
bool IsObjectConstraintActive(const ClassObject* obj, std::string_view name) {
  if (const ClassTypeInfo* owner = StaticConstraintOwner(obj, name)) {
    auto it = owner->static_constraint_active.find(std::string(name));
    return it == owner->static_constraint_active.end() ? true : it->second;
  }
  auto it = obj->constraint_active.find(std::string(name));
  return it == obj->constraint_active.end() ? true : it->second;
}

// 18.9 / Table 18-4: record a block's active (ON) or inactive (OFF) state for
// this object, as set by a void-form constraint_mode() call.
// 18.5.10: a static block's state is written to the class-wide map, so the
// change takes effect for every instance of the declaring class.
void SetObjectConstraintActive(ClassObject* obj, std::string_view name,
                               bool active) {
  if (const ClassTypeInfo* owner = StaticConstraintOwner(obj, name)) {
    owner->static_constraint_active[std::string(name)] = active;
    return;
  }
  obj->constraint_active[std::string(name)] = active;
}

// 18.9: match a constraint_mode() method call and pull out the object handle
// name and, for the named form obj.constraint_id.constraint_mode(...), the
// constraint block name. The no-name form obj.constraint_mode(...) leaves
// constraint_name empty. Returns false for any other call so normal method
// dispatch proceeds.
bool ExtractConstraintModeParts(const Expr* expr, std::string_view& obj_name,
                                std::string_view& constraint_name) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  const Expr* callee = expr->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier) return false;
  if (callee->rhs->text != "constraint_mode") return false;

  const Expr* recv = callee->lhs;
  if (!recv) return false;
  // No-name form: the receiver is the object handle itself.
  if (recv->kind == ExprKind::kIdentifier) {
    obj_name = recv->text;
    constraint_name = {};
    return true;
  }
  // Named form: the receiver is object.constraint_id.
  if (recv->kind == ExprKind::kMemberAccess && recv->lhs &&
      recv->lhs->kind == ExprKind::kIdentifier && recv->rhs &&
      recv->rhs->kind == ExprKind::kIdentifier) {
    obj_name = recv->lhs->text;
    constraint_name = recv->rhs->text;
    return true;
  }
  return false;
}

// 18.8: report whether a random variable is active on this object. Every
// rand/randc variable is active when the object is created, so an absent entry
// means active; an explicit entry records the last rand_mode() setting.
bool IsObjectRandActive(const ClassObject* obj, std::string_view name) {
  auto it = obj->rand_active.find(std::string(name));
  return it == obj->rand_active.end() ? true : it->second;
}

// 18.8 / Table 18-3: record a random variable's active (ON) or inactive (OFF)
// state for this object, as set by a rand_mode() call.
void SetObjectRandActive(ClassObject* obj, std::string_view name, bool active) {
  obj->rand_active[std::string(name)] = active;
}

// 18.8: match a rand_mode() method call and pull out the object handle name
// and, for the named form obj.random_variable.rand_mode(...), the variable
// name. The no-name form obj.rand_mode(...) leaves var_name empty. Returns
// false for any other call so normal method dispatch proceeds.
bool ExtractRandModeParts(const Expr* expr, std::string_view& obj_name,
                          std::string_view& var_name) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  const Expr* callee = expr->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier) return false;
  if (callee->rhs->text != "rand_mode") return false;

  const Expr* recv = callee->lhs;
  if (!recv) return false;
  // No-name form: the receiver is the object handle itself.
  if (recv->kind == ExprKind::kIdentifier) {
    obj_name = recv->text;
    var_name = {};
    return true;
  }
  // Named form: the receiver is object.random_variable.
  if (recv->kind == ExprKind::kMemberAccess && recv->lhs &&
      recv->lhs->kind == ExprKind::kIdentifier && recv->rhs &&
      recv->rhs->kind == ExprKind::kIdentifier) {
    obj_name = recv->lhs->text;
    var_name = recv->rhs->text;
    return true;
  }
  return false;
}

// 18.5.11: gather the identifiers a constraint relation names, partitioned by
// whether the identifier appears in a function-call argument position. 'in_arg'
// is true while descending through the argument subtrees of a call, so a name
// used as (or inside) a function argument is added to 'arg_names' while every
// named identifier is added to 'all_names'. Only the argument subtrees carry
// the in-argument flag; the callee and receiver of a member call do not, so the
// object handle of a qualified call is not mistaken for an argument. The caller
// filters these against the object's random variables.
void CollectConstraintArgRefs(const Expr* e, bool in_arg,
                              std::unordered_set<std::string>& all_names,
                              std::unordered_set<std::string>& arg_names) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) {
    all_names.insert(std::string(e->text));
    if (in_arg) arg_names.insert(std::string(e->text));
  }
  const bool call = e->kind == ExprKind::kCall;
  CollectConstraintArgRefs(e->lhs, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->rhs, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->condition, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->true_expr, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->false_expr, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->base, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->index, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->index_end, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->with_expr, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->repeat_count, in_arg, all_names, arg_names);
  // A call's arguments (and everything nested within them) are in-argument.
  for (const Expr* a : e->args)
    CollectConstraintArgRefs(a, call || in_arg, all_names, arg_names);
  for (const Expr* el : e->elements)
    CollectConstraintArgRefs(el, in_arg, all_names, arg_names);
}

void AddConstraintMember(const ClassMember* m, std::vector<RandInfo>& rands,
                         RandomizeCtx& rc, ConstraintSolver& solver) {
  ConstraintBlock block;
  block.name = std::string(m->name);
  block.constraints.reserve(
      m->constraint_exprs.size() + m->constraint_dist_refs.size() +
      m->constraint_soft_exprs.size() + m->constraint_soft_dist_refs.size());
  for (const Expr* rel : m->constraint_exprs) {
    block.constraints.push_back(TranslateRelation(rel, rands, rc));
  }
  // 18.5.3: build each captured distribution as a weighted-value constraint.
  for (const auto& ref : m->constraint_dist_refs) {
    ConstraintExpr ce;
    if (BuildDistConstraint(ref, rc, ce)) block.constraints.push_back(ce);
  }
  // 18.5.13: build each captured soft constraint. The inner relation is
  // translated exactly like a hard one but without folding the draw domain,
  // then wrapped in a kSoft constraint. The solver seeds the inner so a
  // satisfiable preference is honored, yet discards the soft (treating it as
  // the value 1) and never fails the solve when the preference conflicts with
  // the hard constraints. The inner is heap-owned in rc so the kSoft's raw
  // pointer to it stays valid after the block is copied into the solver.
  for (const Expr* rel : m->constraint_soft_exprs) {
    auto inner = std::make_unique<ConstraintExpr>(
        TranslateRelation(rel, rands, rc, /*fold=*/false));
    ConstraintExpr sc;
    sc.kind = ConstraintKind::kSoft;
    sc.var_name = inner->var_name;
    sc.ref_vars = inner->ref_vars;
    sc.inner = inner.get();
    rc.soft_inners.push_back(std::move(inner));
    block.constraints.push_back(std::move(sc));
  }
  // 18.5.13: a 'soft'-prefixed distribution wraps the dist alternative of the
  // soft operand. Build the inner as an ordinary weighted-value (kDist)
  // constraint, then wrap it in a kSoft: the solver seeds the distribution when
  // it is honored and discards it (leaving its variable free) when it conflicts
  // with the hard constraints.
  for (const auto& ref : m->constraint_soft_dist_refs) {
    auto inner = std::make_unique<ConstraintExpr>();
    if (!BuildDistConstraint(ref, rc, *inner)) continue;
    ConstraintExpr sc;
    sc.kind = ConstraintKind::kSoft;
    sc.var_name = inner->var_name;
    sc.ref_vars.push_back(inner->var_name);
    sc.inner = inner.get();
    rc.soft_inners.push_back(std::move(inner));
    block.constraints.push_back(std::move(sc));
  }
  // 18.5.4: build each captured uniqueness constraint as a kUnique solver
  // constraint. Each range_list member that names an active rand variable is
  // resolved to that solver variable; the solver then requires the named
  // variables to hold pairwise-distinct values, enforces the no-randc and
  // equivalent-type restrictions on the group, and treats a group of fewer than
  // two known members as having no effect. A member the solver does not model
  // as its own variable (e.g. an array slice, whose elements the scalar solver
  // does not draw individually) is left out of the group, mirroring the lenient
  // treatment of unknown references elsewhere in the translation.
  for (const auto& group : m->constraint_unique_refs) {
    ConstraintExpr ce;
    ce.kind = ConstraintKind::kUnique;
    for (const Expr* item : group) {
      if (item != nullptr && item->kind == ExprKind::kIdentifier &&
          FindRand(rands, item->text)) {
        ce.unique_vars.push_back(std::string(item->text));
      }
    }
    ce.ref_vars = ce.unique_vars;
    block.constraints.push_back(std::move(ce));
  }

  // 18.5.9: lower each 'solve before_list before after_list' ordering into the
  // solver's variable ordering. Only a simple local entry that resolves to an
  // active rand variable participates; a qualified reference or an array.size()
  // method — which the scalar solver does not model as its own drawable
  // variable — is left out, mirroring the lenient treatment of unresolved
  // references in the uniqueness lowering above. The ordering only reweights
  // the probability of the legal combinations and never removes a solution, so
  // dropping an unresolved entry merely relaxes the order rather than losing a
  // solution.
  for (const auto& ref : m->constraint_solve_before_refs) {
    std::vector<std::string> before;
    std::vector<std::string> after;
    for (const auto& e : ref.before)
      if (e.is_simple && FindRand(rands, e.name))
        before.push_back(std::string(e.name));
    for (const auto& e : ref.after)
      if (e.is_simple && FindRand(rands, e.name))
        after.push_back(std::string(e.name));
    if (!before.empty() && !after.empty()) solver.AddSolveBefore(before, after);
  }

  // 18.5.11: a random variable used as a function argument in a constraint
  // establishes an implicit priority — it is solved ahead of the variables of
  // the constraint that consumes it, and its committed value is then read as a
  // state variable when the function is called for the lower-priority set. For
  // each hard relation, the rand variables appearing in a function-call
  // argument position outrank the rand variables the relation uses directly, so
  // record that ordering for the solver's priority-layer pass. Only variables
  // the solver models as its own drawable variable participate, mirroring the
  // lenient treatment of unresolved references in the orderings above. A
  // variable used directly is excluded from the lower set of the same relation
  // when it also supplies an argument there, so a self-reference does not
  // fabricate a degenerate cycle; a genuine cycle across relations (each uses
  // the other as an argument) still forms and is rejected by SolveWith.
  for (const Expr* rel : m->constraint_exprs) {
    std::unordered_set<std::string> all_names;
    std::unordered_set<std::string> arg_names;
    CollectConstraintArgRefs(rel, /*in_arg=*/false, all_names, arg_names);
    std::vector<std::string> higher;
    for (const auto& n : arg_names)
      if (FindRand(rands, n)) higher.push_back(n);
    if (higher.empty()) continue;
    std::vector<std::string> lower;
    for (const auto& n : all_names)
      if (arg_names.find(n) == arg_names.end() && FindRand(rands, n))
        lower.push_back(n);
    if (!lower.empty()) solver.AddFunctionArgPriority(higher, lower);
  }

  // 18.9: a block turned inactive by constraint_mode() is not considered by
  // randomize(); it is created active, so an unset block stays enabled.
  block.enabled = IsObjectConstraintActive(rc.obj, m->name);
  solver.AddConstraintBlock(block);
}

// 18.5/18.5.2: build the constraint block(s) from the captured relations of
// every constraint member on the object's class hierarchy. Walking from the
// dynamic type up to its base classes, the first constraint seen for a given
// name is the most-derived one; 18.5.2 says a same-named constraint in a
// derived class replaces the inherited one, so a base constraint of a name
// already contributed by a more-derived level is skipped rather than added
// alongside it. The name is recorded even for an empty (no-effect) derived
// constraint so that it, too, replaces the inherited one.
void CollectConstraintBlocks(const ClassTypeInfo* type,
                             std::vector<RandInfo>& rands, RandomizeCtx& rc,
                             ConstraintSolver& solver) {
  // Walk from the dynamic type up to its base classes so the first constraint
  // seen for a given name is the most-derived one (18.5.2: a same-named derived
  // constraint replaces the inherited one). Buffer the members to build per
  // level rather than adding them as they are seen, so the levels can be added
  // to the solver in a different order than they are scanned.
  std::unordered_set<std::string_view> replaced;
  std::vector<std::vector<const ClassMember*>> per_level;
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    std::vector<const ClassMember*> level_members;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind != ClassMemberKind::kConstraint) continue;
      if (!replaced.insert(m->name).second) continue;
      if (!m->constraint_exprs.empty() || !m->constraint_dist_refs.empty() ||
          !m->constraint_soft_exprs.empty() ||
          !m->constraint_soft_dist_refs.empty() ||
          !m->constraint_unique_refs.empty() ||
          !m->constraint_solve_before_refs.empty())
        level_members.push_back(m);
    }
    per_level.push_back(std::move(level_members));
  }
  // 18.5.13.1: constraints in a derived class have higher soft-constraint
  // priority than all constraints in its superclasses. The solver ranks soft
  // priority by the order blocks are added — a block added later outranks an
  // earlier one — so add the levels base class first and the most-derived level
  // last. per_level was filled most-derived first, so walk it in reverse. This
  // reordering is confined to soft-constraint priority: hard constraints must
  // all hold regardless of order, and the ordering/priority edges (18.5.9,
  // 18.5.11) are order-independent sets, so the solutions are unchanged. Within
  // a level the members keep their syntactic declaration order, which fixes
  // their relative priority.
  for (auto it = per_level.rbegin(); it != per_level.rend(); ++it)
    for (const ClassMember* m : *it) AddConstraintMember(m, rands, rc, solver);
}

// Resolve the concrete object from the handle. Works equally for a direct class
// handle and an interface-class handle (8.26.9): the dynamic object found from
// the handle is the implementing class instance either way.
ClassObject* ResolveRandomizeTarget(SimContext& ctx,
                                    const MethodCallParts& parts) {
  if (ctx.GetVariableClassType(parts.var_name).empty()) return nullptr;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return nullptr;
  uint64_t handle = var->value.ToUint64();
  if (handle == kNullClassHandle) return nullptr;
  ClassObject* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type) return nullptr;
  return obj;
}

// 18.6.2: pre_randomize() is invoked by randomize() before any new random value
// is computed. Register it as the solver's pre hook, which fires ahead of the
// solve. The method is resolved on the object's actual (dynamic) class: because
// randomize() is virtual, an override in the dynamic type is reached even
// through a base-class handle, so pre_randomize() appears to behave virtually.
// A derived class that does not itself declare pre_randomize() resolves to the
// inherited one, which is the effect of automatically invoking
// super.pre_randomize().
void RegisterPreRandomize(ClassObject* obj, const Expr* expr, SimContext& ctx,
                          Arena& arena, ConstraintSolver& solver) {
  const ClassTypeInfo* owner = nullptr;
  if (ModuleItem* pre =
          obj->ResolveMethodForType("pre_randomize", obj->type, &owner)) {
    // Run the body with its defining class as the enclosing scope so an
    // unqualified member resolves to that level (§8.15) and a super call inside
    // an override walks one level up, mirroring an ordinary method dispatch.
    solver.SetPreRandomize([pre, obj, owner, expr, &ctx, &arena] {
      ctx.PushMethodClass(owner);
      ExecInstanceMethodCall(pre, obj, expr, ctx, arena);
      ctx.PopMethodClass();
    });
  }
}

// 18.6.2: post_randomize() is invoked by randomize() after the new random
// values have been computed AND assigned back to the object, so a user
// post_randomize() reads the just-randomized members at their new values. It is
// therefore called by the caller only after WriteBackSolved has published the
// solved values, and only on a successful solve (18.6.3 skips it on failure).
// Like pre_randomize() it is resolved on the dynamic class, giving the same
// apparent-virtual and inherited-implementation behavior.
void InvokePostRandomize(ClassObject* obj, const Expr* expr, SimContext& ctx,
                         Arena& arena) {
  const ClassTypeInfo* owner = nullptr;
  if (ModuleItem* post =
          obj->ResolveMethodForType("post_randomize", obj->type, &owner)) {
    ctx.PushMethodClass(owner);
    ExecInstanceMethodCall(post, obj, expr, ctx, arena);
    ctx.PopMethodClass();
  }
}

// 18.6.1: write each solved value back to the object, keeping the bare and
// scoped ("Class::name") property aliases in sync so member reads see it.
void WriteBackSolved(ClassObject* obj, std::vector<RandInfo>& rands,
                     ConstraintSolver& solver, Arena& arena) {
  for (auto& ri : rands) {
    if (ri.var.is_real) continue;
    int64_t v = solver.GetValue(ri.name);
    Logic4Vec lv =
        MakeLogic4VecVal(arena, ri.var.width, static_cast<uint64_t>(v));
    obj->properties[ri.name] = lv;
    obj->properties[std::string(ri.level->name) + "::" + ri.name] = lv;
  }
}

// 18.6.1: enumerate the rand/randc class-handle members visible on the object.
// Each such member names a sub-object: because randomize() sets "all the random
// variables and objects", every referenced object is randomized in turn. Walk
// the inheritance chain so inherited random object handles are included.
void CollectRandObjectMembers(const ClassTypeInfo* type, SimContext& ctx,
                              std::vector<std::string>& out) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kProperty &&
          (m->is_rand || m->is_randc) && IsClassHandleMember(m, ctx))
        out.push_back(std::string(m->name));
    }
  }
}

// 18.11: the property name that a randomize() inline-control argument refers
// to. Such an argument is a plain property reference -- a bare identifier, an
// indexed element, or a member access -- never a computed expression (the
// parser has already rejected those). Returns the referenced name, or an empty
// view for a form that carries none.
std::string_view InlineRandomArgName(const Expr* arg) {
  if (arg == nullptr) return {};
  switch (arg->kind) {
    case ExprKind::kIdentifier:
      return arg->text;
    case ExprKind::kSelect:
      return InlineRandomArgName(arg->base);
    case ExprKind::kMemberAccess:
      return InlineRandomArgName(arg->rhs);
    default:
      return {};
  }
}

// 18.11: locate a class property by name for the inline random control list,
// walking the inheritance chain. Unlike CollectRandVariables this ignores the
// rand/randc qualifier, because naming a property in the argument list may make
// even a non-random property one of the object's random variables. Class-handle
// members are excluded so the handle they hold is never overwritten.
const ClassMember* FindNamedProperty(const ClassTypeInfo* type, SimContext& ctx,
                                     std::string_view name,
                                     const ClassTypeInfo** out_level) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kProperty &&
          std::string_view(m->name) == name && !IsClassHandleMember(m, ctx)) {
        if (out_level != nullptr) *out_level = lvl;
        return m;
      }
    }
  }
  return nullptr;
}

// 18.6.1: randomize() sets all of an object's active random variables AND the
// random objects it references to valid values, succeeding only when every one
// is solved. Solve this object's own random variables subject to its active
// constraints and write the results back, then recurse into each non-null rand
// object-handle member so its own random members are randomized as well; the
// overall result fails if any sub-object solve fails. The visited set breaks
// handle cycles so a self- or mutually-referential object graph terminates. A
// null random object handle references nothing to randomize and is skipped.
//
// 18.11: inline_random, when non-null, is the set of property names passed as
// randomize()'s arguments. It names the complete active random set for the
// duration of this one call: a named property is active (and a non-random
// property so named is promoted to a random variable), while every other
// variable becomes a state variable held at its current value. It governs only
// the object named in the call, so it is passed as null on the recursive
// descent into rand sub-objects below.
//
// 18.11.1: null_checker marks the special randomize(null) form, the inline
// constraint checker. It rides on top of the same mechanism: inline_random is
// an empty (but present) set, so every rand/randc variable is excluded from the
// active set and held as a state variable, and no value is drawn for the call.
// Because no class member is randomized, the rand object-handle members are not
// recursed into either -- they too are state variables for this call.
bool RandomizeObject(ClassObject* obj, SimContext& ctx, Arena& arena,
                     const Expr* expr, const ClassMember* inline_block,
                     const std::unordered_set<std::string>* inline_random,
                     bool null_checker,
                     std::unordered_set<const ClassObject*>& visited) {
  if (!obj || !obj->type) return false;
  if (!visited.insert(obj).second) return true;

  // 18.6.3: seed from the object's own RNG so randomize() draws a fresh result
  // each call while staying reproducible from the object's starting state.
  auto seed = static_cast<uint32_t>(ctx.ObjectRng(obj)());
  ConstraintSolver solver(seed);
  RandomizeCtx rc{obj, ctx, arena};

  std::vector<RandInfo> rands;
  CollectRandVariables(obj->type, ctx, rands);
  // 18.11: naming a property in the inline argument list can change the random
  // mode of any class property, even one not declared rand or randc. A named
  // property that is not already among the rand/randc set is looked up and
  // added as an active random variable so it is solved and written back like
  // any other. It is added before the constraint blocks are gathered so a
  // constraint relating to it binds it as a random variable rather than a state
  // constant. The mechanism does not affect the cyclical mode, so the promoted
  // variable is built as a noncyclical rand (AddRandMember keys the qualifier
  // off the member's own randc declaration, which a non-random property does
  // not have).
  if (inline_random != nullptr) {
    for (const auto& nm : *inline_random) {
      if (FindRand(rands, nm) != nullptr) continue;
      const ClassTypeInfo* lvl = nullptr;
      if (const ClassMember* m = FindNamedProperty(obj->type, ctx, nm, &lvl))
        AddRandMember(m, lvl, ctx, rands);
    }
  }
  CollectConstraintBlocks(obj->type, rands, rc, solver);
  // 18.7: the inline constraint block from a randomize() with {...} call is
  // applied along with the object's own constraints -- not in place of them. It
  // is translated into an additional, always-active constraint block using the
  // same machinery as an in-class block, so its relations (and
  // dist/soft/if-else forms) narrow this object's solve exactly like a class
  // constraint. It is applied only to the object named in the call, not to its
  // rand sub-objects, so inline_block is passed as null on the recursive
  // descent below.
  if (inline_block != nullptr) {
    // 18.7: a block preceded by a parenthesized identifier_list is restricted
    // -- only the listed names resolve as the object's random variables; every
    // other name resolves in the calling scope. Translating the block against a
    // rand set filtered to the listed names realizes exactly that: an unlisted
    // name is not found among the rand variables, so it is read from the caller
    // as a constant instead of being treated as one of the object's randoms. An
    // unrestricted block (no parentheses) sees the full rand set.
    if (expr != nullptr && expr->with_has_parens) {
      std::unordered_set<std::string_view> listed(
          expr->with_restrict_ids.begin(), expr->with_restrict_ids.end());
      std::vector<RandInfo> listed_rands;
      for (const auto& ri : rands)
        if (listed.count(ri.name) != 0) listed_rands.push_back(ri);
      AddConstraintMember(inline_block, listed_rands, rc, solver);
    } else {
      AddConstraintMember(inline_block, rands, rc, solver);
    }
  }
  for (auto& ri : rands) {
    if (ri.var.min_val > ri.var.max_val) ri.var.max_val = ri.var.min_val;
    // 18.4.2: a randc variable shall not repeat a value until its permutation
    // is exhausted, and that no-repeat property spans successive randomize()
    // calls. Because the solver is rebuilt for every call, hand it a persistent
    // permutation history to advance in place so the cycle continues across
    // calls instead of restarting each time. A nonstatic randc uses this
    // object's own per-member history; a static randc shares one history held
    // on the (single, per-class) type descriptor, so its cyclic state is static
    // too — a single sequence advances no matter which instance is randomized.
    if (ri.var.qualifier == RandQualifier::kRandc) {
      std::shared_ptr<std::unordered_set<int64_t>>* slot =
          (ri.is_static && ri.level) ? &ri.level->static_randc_history[ri.name]
                                     : &obj->randc_history[ri.name];
      if (!*slot) *slot = std::make_shared<std::unordered_set<int64_t>>();
      ri.var.shared_randc_state = *slot;
    }
    // 18.11: when randomize() is called with an argument list, those arguments
    // designate the complete set of random variables for this call and every
    // other variable is considered a state variable -- conceptually equivalent
    // to rand_mode() calls that enable the named variables and disable the
    // rest. The inline list therefore fully governs the active set here,
    // overriding the persistent rand_mode() state for the duration of the call.
    // Without an argument list (18.8) the persistent per-object rand_mode()
    // flag governs.
    bool active = inline_random != nullptr ? inline_random->count(ri.name) != 0
                                           : IsObjectRandActive(obj, ri.name);
    // 18.8 / 18.11: a variable that is not active is not randomized; the solver
    // treats it as a state variable, holding its current value constant. Seed
    // that value and disable the variable so the solve leaves it untouched
    // while still evaluating any constraint that relates to it.
    if (!active) {
      auto pit = obj->properties.find(ri.name);
      if (pit != obj->properties.end())
        ri.var.value = static_cast<int64_t>(pit->second.ToUint64());
      ri.var.enabled = false;
    }
    solver.AddVariable(ri.var);
  }
  RegisterPreRandomize(obj, expr, ctx, arena, solver);

  bool solved = solver.SolveWith({});
  // 18.6.2: post_randomize() must observe the new values as assigned to the
  // object, so write the solved values back first and only then invoke it. The
  // solver's pre hook already fired before the compute; post is sequenced here,
  // after the writeback, rather than inside the solve.
  if (solved) {
    WriteBackSolved(obj, rands, solver, arena);
    InvokePostRandomize(obj, expr, ctx, arena);
  }

  // 18.11.1: under randomize(null) nothing is randomized, so a rand
  // object-handle member is a state variable and the object it references is
  // left untouched -- do not recurse into it.
  std::vector<std::string> object_members;
  if (!null_checker) CollectRandObjectMembers(obj->type, ctx, object_members);
  for (const auto& name : object_members) {
    // 18.8: rand_mode() on a rand object-handle member changes only that
    // handle's mode. An inactive handle is not one of the object's active
    // random variables, so randomize() does not recurse into the object it
    // references; the referenced object's own variable modes are left as they
    // are (only reached by randomizing that object directly).
    if (!IsObjectRandActive(obj, name)) continue;
    auto it = obj->properties.find(name);
    if (it == obj->properties.end()) continue;
    uint64_t handle = it->second.ToUint64();
    if (handle == kNullClassHandle) continue;
    ClassObject* sub = ctx.GetClassObject(handle);
    if (!sub) continue;
    if (!RandomizeObject(sub, ctx, arena, expr, /*inline_block=*/nullptr,
                         /*inline_random=*/nullptr, /*null_checker=*/false,
                         visited))
      solved = false;
  }
  return solved;
}

// 18.5.8: one active random object taking part in a joint solve, paired with
// the dotted path prefix under which its variables and constraints are named in
// the single shared solver. The root object has an empty prefix; an object
// reached through the root's rand handle 'h' has prefix "h.", one two levels
// down "h.g.", and so on.
struct JointObject {
  ClassObject* obj;
  std::string prefix;
};

// 18.5.8 rule a: determine the set of objects to be randomized as a whole.
// Starting from the object that invoked randomize(), add every object it
// contains through a rand class-handle member that is itself active (18.8) and
// non-null; recurse so the definition reaches the whole tree of active random
// objects. The visited set breaks handle cycles so a self- or mutually
// referential graph terminates.
void CollectActiveRandomObjects(
    ClassObject* obj, const std::string& prefix, SimContext& ctx,
    std::vector<JointObject>& out,
    std::unordered_set<const ClassObject*>& visited) {
  if (!obj || !obj->type) return;
  if (!visited.insert(obj).second) return;
  out.push_back({obj, prefix});

  std::vector<std::string> handles;
  CollectRandObjectMembers(obj->type, ctx, handles);
  for (const auto& name : handles) {
    // 18.8: an inactive rand handle is not one of the object's active random
    // variables, so the object it references is not part of the active set.
    if (!IsObjectRandActive(obj, name)) continue;
    auto it = obj->properties.find(name);
    if (it == obj->properties.end()) continue;
    uint64_t handle = it->second.ToUint64();
    if (handle == kNullClassHandle) continue;
    ClassObject* sub = ctx.GetClassObject(handle);
    if (!sub) continue;
    CollectActiveRandomObjects(sub, prefix + name + ".", ctx, out, visited);
  }
}

// 18.5.8 rule c: gather the active random variables of every object in the tree
// into one joint table. Each object's own rand/randc data members are given a
// path-qualified solver name so members that share a plain name on different
// objects never collide. The solver domain is bound to the declared width: a
// value drawn to satisfy a custom global constraint is checked at full width,
// so pinning the domain to the member width keeps the write-back truncation
// from turning a satisfying assignment into a violating one.
void CollectJointRandVariables(const std::vector<JointObject>& objects,
                               SimContext& ctx, std::vector<RandInfo>& out) {
  for (const auto& jo : objects) {
    std::vector<RandInfo> local;
    CollectRandVariables(jo.obj->type, ctx, local);
    for (auto& ri : local) {
      ri.member = ri.name;
      ri.owner = jo.obj;
      ri.name = jo.prefix + ri.name;
      ri.var.name = ri.name;
      uint32_t w = ri.var.width;
      ri.var.min_val = 0;
      ri.var.max_val =
          w >= 63 ? INT64_MAX : ((static_cast<int64_t>(1) << w) - 1);
      out.push_back(std::move(ri));
    }
  }
}

// 18.5.8: resolve a constraint operand to the path-qualified name of a joint
// rand variable, or an empty string when the operand is not one (so it is a
// state variable, whose current value is a constant). A bare identifier names a
// rand member of the constraint's own object -- prefix + id. A one-level
// handle.field member access names a rand member of a nested object reached
// through the owner's rand handle -- prefix + handle + "." + field. Only names
// present in the joint set qualify; everything else is a constant.
std::string ResolveJointOperand(const Expr* e, const std::string& prefix,
                                const std::unordered_set<std::string>& names) {
  if (e == nullptr) return {};
  if (e->kind == ExprKind::kIdentifier) {
    std::string q = prefix + std::string(e->text);
    return names.count(q) != 0 ? q : std::string{};
  }
  if (e->kind == ExprKind::kMemberAccess && e->lhs != nullptr &&
      e->lhs->kind == ExprKind::kIdentifier && e->rhs != nullptr &&
      e->rhs->kind == ExprKind::kIdentifier) {
    std::string q =
        prefix + std::string(e->lhs->text) + "." + std::string(e->rhs->text);
    return names.count(q) != 0 ? q : std::string{};
  }
  return {};
}

// 18.5.8: true when an expression references any joint rand variable, so it is
// not a solve-time constant. A member access is resolved as a whole -- its
// field identifier is never treated as a bare-identifier operand, so a nested
// `.v` is not confused with a same-named variable of the constraint's own
// object.
bool RefsJointVar(const Expr* e, const std::string& prefix,
                  const std::unordered_set<std::string>& names) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kMemberAccess)
    return !ResolveJointOperand(e, prefix, names).empty();
  if (RefsJointVar(e->lhs, prefix, names)) return true;
  if (RefsJointVar(e->rhs, prefix, names)) return true;
  if (RefsJointVar(e->base, prefix, names)) return true;
  for (const Expr* a : e->args)
    if (RefsJointVar(a, prefix, names)) return true;
  return false;
}

// 18.5.8: collect the qualified names of the joint variables an expression
// references (for the priority/ordered passes; the flat pass checks every
// constraint regardless). A member access is taken atomically so its field is
// not walked as a separate identifier.
void CollectJointRefs(const Expr* e, const std::string& prefix,
                      const std::unordered_set<std::string>& names,
                      std::vector<std::string>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kMemberAccess) {
    std::string q = ResolveJointOperand(e, prefix, names);
    if (!q.empty()) out.push_back(q);
    return;
  }
  CollectJointRefs(e->lhs, prefix, names, out);
  CollectJointRefs(e->rhs, prefix, names, out);
  CollectJointRefs(e->base, prefix, names, out);
  for (const Expr* a : e->args) CollectJointRefs(a, prefix, names, out);
}

// 18.5.8: build a custom joint constraint. A global constraint relates random
// variables from different objects, so it cannot fold one side into a domain
// bound; instead it is checked against trial values. On each evaluation the
// trial value of every joint variable is written into its owning object's
// property, the relation is evaluated in the owner's scope so a member access
// like left.v reads the trial value from the referenced object, and the
// original property values are restored. This lets the solver see every
// referenced variable at its trial value simultaneously, which is what "solved
// simultaneously" requires.
ConstraintExpr MakeJointCustomConstraint(
    const Expr* rel, const std::string& prefix, ClassObject* owner,
    std::vector<RandInfo>& rands, const std::unordered_set<std::string>& names,
    RandomizeCtx& rc) {
  ConstraintExpr ce;
  ce.kind = ConstraintKind::kCustom;
  CollectJointRefs(rel, prefix, names, ce.ref_vars);
  std::vector<RandInfo>* jr = &rands;
  ce.eval_fn = [rel, owner, jr,
                &rc](const std::unordered_map<std::string, int64_t>& vals) {
    struct Saved {
      ClassObject* obj;
      std::string key;
      bool had;
      Logic4Vec old;
    };
    std::vector<Saved> saved;
    auto stash = [&](ClassObject* o, const std::string& key,
                     const Logic4Vec& nv) {
      auto pit = o->properties.find(key);
      saved.push_back({o, key, pit != o->properties.end(),
                       pit != o->properties.end() ? pit->second : Logic4Vec{}});
      o->properties[key] = nv;
    };
    for (auto& ri : *jr) {
      auto vit = vals.find(ri.name);
      if (vit == vals.end()) continue;
      Logic4Vec nv = MakeLogic4VecVal(rc.arena, ri.var.width,
                                      static_cast<uint64_t>(vit->second));
      stash(ri.owner, ri.member, nv);
      if (ri.level != nullptr)
        stash(ri.owner, std::string(ri.level->name) + "::" + ri.member, nv);
    }
    rc.ctx.PushScope();
    rc.ctx.PushThis(owner);
    Logic4Vec r = EvalExpr(rel, rc.ctx, rc.arena);
    rc.ctx.PopThis();
    rc.ctx.PopScope();
    for (auto it = saved.rbegin(); it != saved.rend(); ++it) {
      if (it->had)
        it->obj->properties[it->key] = it->old;
      else
        it->obj->properties.erase(it->key);
    }
    return r.IsTruthy();
  };
  return ce;
}

// 18.5.8: translate one relation of an object's constraint for the joint solve.
// A comparison whose other side is a genuine constant (no joint variable) keeps
// the folding/seeding fast path -- qualified to the owner's path and evaluated
// in the owner's scope -- so an equality or bound is still hit reliably; this
// is also how a global constraint against a state variable (rule c) is handled,
// its held value folded in as the constant. Any relation that ties two joint
// variables together, or that is not a plain comparison, becomes a custom joint
// constraint checked against trial values.
ConstraintExpr BuildJointRelation(const Expr* rel, const std::string& prefix,
                                  ClassObject* owner,
                                  std::vector<RandInfo>& rands,
                                  const std::unordered_set<std::string>& names,
                                  RandomizeCtx& rc) {
  if (rel != nullptr && rel->kind == ExprKind::kBinary && rel->lhs != nullptr &&
      rel->rhs != nullptr) {
    ConstraintKind kind = ConstraintKind::kEqual;
    if (ComparisonKind(rel->op, kind)) {
      std::string lname = ResolveJointOperand(rel->lhs, prefix, names);
      std::string rname = ResolveJointOperand(rel->rhs, prefix, names);
      std::string vname;
      const Expr* const_side = nullptr;
      bool mirror = false;
      if (!lname.empty() && !RefsJointVar(rel->rhs, prefix, names)) {
        vname = lname;
        const_side = rel->rhs;
      } else if (!rname.empty() && !RefsJointVar(rel->lhs, prefix, names)) {
        vname = rname;
        const_side = rel->lhs;
        mirror = true;
      }
      if (!vname.empty()) {
        if (mirror) ComparisonKind(MirrorComparison(rel->op), kind);
        rc.ctx.PushScope();
        rc.ctx.PushThis(owner);
        auto c = static_cast<int64_t>(
            EvalExpr(const_side, rc.ctx, rc.arena).ToUint64());
        rc.ctx.PopThis();
        rc.ctx.PopScope();
        ConstraintExpr out;
        out.kind = kind;
        out.var_name = vname;
        out.lo = c;
        out.ref_vars.push_back(vname);
        if (RandInfo* ri = FindRand(rands, vname)) FoldBound(*ri, kind, c);
        return out;
      }
    }
  }
  return MakeJointCustomConstraint(rel, prefix, owner, rands, names, rc);
}

// 18.5.8 rule b: select the active constraints of every object in the tree.
// Each object's constraint blocks are collected the same way as for a single
// object (a same-named derived block replaces an inherited one) and translated
// into the shared solver. Only relational constraint expressions are carried
// through the joint path; the tree cases that arise relate simple relational
// and equality constraints, so dist/soft/foreach constraints on a nested object
// are left to the per-object path and not reached here.
void CollectJointConstraints(const JointObject& jo,
                             std::vector<RandInfo>& rands,
                             const std::unordered_set<std::string>& names,
                             RandomizeCtx& rc, ConstraintSolver& solver) {
  std::unordered_set<std::string_view> replaced;
  for (const auto* lvl = jo.obj->type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind != ClassMemberKind::kConstraint) continue;
      if (!replaced.insert(m->name).second) continue;
      if (m->constraint_exprs.empty()) continue;
      ConstraintBlock block;
      block.name = std::string(m->name);
      for (const Expr* rel : m->constraint_exprs)
        block.constraints.push_back(
            BuildJointRelation(rel, jo.prefix, jo.obj, rands, names, rc));
      // 18.9: a block turned off by constraint_mode() is not considered.
      block.enabled = IsObjectConstraintActive(jo.obj, m->name);
      solver.AddConstraintBlock(block);
    }
  }
}

// 18.5.8: randomize the whole active random object tree as one problem. A
// single solver holds every active random variable (rule c) and every active
// constraint (rule b) of every active random object (rule a), so global
// constraints that relate variables from different objects are solved
// simultaneously. The result is written back to each object, and 18.6.2's
// pre/post_randomize() fire on the object and on each of its random object
// members.
bool RandomizeObjectTree(SimContext& ctx, Arena& arena, const Expr* expr,
                         const std::vector<JointObject>& objects) {
  ClassObject* root = objects.front().obj;
  auto seed = static_cast<uint32_t>(ctx.ObjectRng(root)());
  ConstraintSolver solver(seed);
  RandomizeCtx rc{root, ctx, arena};

  std::vector<RandInfo> rands;
  CollectJointRandVariables(objects, ctx, rands);
  std::unordered_set<std::string> names;
  for (const auto& ri : rands) names.insert(ri.name);

  for (const auto& jo : objects)
    CollectJointConstraints(jo, rands, names, rc, solver);

  for (auto& ri : rands) {
    if (ri.var.min_val > ri.var.max_val) ri.var.max_val = ri.var.min_val;
    // 18.4.2: continue a randc member's cyclic permutation across calls through
    // its persistent history, per object (or per class for a static randc).
    if (ri.var.qualifier == RandQualifier::kRandc) {
      std::shared_ptr<std::unordered_set<int64_t>>* slot =
          (ri.is_static && ri.level)
              ? &ri.level->static_randc_history[ri.member]
              : &ri.owner->randc_history[ri.member];
      if (!*slot) *slot = std::make_shared<std::unordered_set<int64_t>>();
      ri.var.shared_randc_state = *slot;
    }
    // 18.8 / 18.5.8 rule c: a variable made inactive by rand_mode() is not
    // randomized; it holds its current value as a state constant that a global
    // constraint solved alongside it sees as a fixed operand.
    if (!IsObjectRandActive(ri.owner, ri.member)) {
      auto pit = ri.owner->properties.find(ri.member);
      if (pit != ri.owner->properties.end())
        ri.var.value = static_cast<int64_t>(pit->second.ToUint64());
      ri.var.enabled = false;
    }
    solver.AddVariable(ri.var);
  }

  // 18.6.2: pre_randomize() runs on the object and on all of its random object
  // members before any new value is computed. Resolve each on its dynamic class
  // so an override is reached and an absent one inherits the base method.
  std::vector<JointObject> pre_objects(objects);
  solver.SetPreRandomize([pre_objects, expr, &ctx, &arena] {
    for (const auto& jo : pre_objects) {
      const ClassTypeInfo* owner = nullptr;
      if (ModuleItem* pre = jo.obj->ResolveMethodForType(
              "pre_randomize", jo.obj->type, &owner)) {
        ctx.PushMethodClass(owner);
        ExecInstanceMethodCall(pre, jo.obj, expr, ctx, arena);
        ctx.PopMethodClass();
      }
    }
  });

  bool solved = solver.SolveWith({});
  if (solved) {
    for (auto& ri : rands) {
      if (ri.var.is_real) continue;
      int64_t v = solver.GetValue(ri.name);
      Logic4Vec lv =
          MakeLogic4VecVal(arena, ri.var.width, static_cast<uint64_t>(v));
      ri.owner->properties[ri.member] = lv;
      if (ri.level != nullptr)
        ri.owner->properties[std::string(ri.level->name) + "::" + ri.member] =
            lv;
    }
    // 18.6.2: post_randomize() runs after the new values are written back, so
    // each object's post_randomize() reads its members at their solved values.
    for (const auto& jo : objects)
      InvokePostRandomize(jo.obj, expr, ctx, arena);
  }
  return solved;
}

}  // namespace

bool TryEvalRandomizeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.method_name != "randomize") return false;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // 18.11: a randomize() argument list names the object properties that make up
  // the active random set for this call. Collect those names; an unnamed rand
  // variable becomes a state variable and a named non-random property becomes a
  // random one.
  //
  // 18.11.1: the special argument null designates no random variables for the
  // duration of the call -- every class member, even one declared rand or
  // randc, behaves as a state variable. This turns randomize() into an inline
  // constraint checker that evaluates all constraints against the current
  // values and returns 1 when they all hold and 0 otherwise, drawing no new
  // value. An empty (but present) active set realizes exactly that: no variable
  // is in it, so each is disabled and held at its current value in
  // RandomizeObject, and the null_checker flag additionally holds any rand
  // sub-object as state.
  std::unordered_set<std::string> inline_random;
  bool has_inline_list = false;
  bool null_checker = false;
  for (const Expr* arg : expr->args) {
    if (arg != nullptr && arg->kind == ExprKind::kIdentifier &&
        arg->text == "null") {
      null_checker = true;
      inline_random.clear();
      has_inline_list = false;
      break;
    }
    std::string_view nm = InlineRandomArgName(arg);
    if (!nm.empty()) {
      inline_random.insert(std::string(nm));
      has_inline_list = true;
    }
  }

  std::unordered_set<const ClassObject*> visited;
  // 18.5.8: the plain randomize() form randomizes the object together with all
  // of its active random object members as a single whole, so global
  // constraints relating variables from different objects are solved
  // simultaneously. When the active random object set (rule a) has more than
  // the root object, solve the tree jointly. The argument-list form (18.11),
  // the null checker (18.11.1) and an inline (with) block keep the per-object
  // path.
  if (!null_checker && !has_inline_list && expr->inline_constraint == nullptr) {
    std::vector<JointObject> objects;
    CollectActiveRandomObjects(obj, "", ctx, objects, visited);
    if (objects.size() > 1) {
      bool ok = RandomizeObjectTree(ctx, arena, expr, objects);
      out = MakeLogic4VecVal(arena, 32, ok ? 1 : 0);
      return true;
    }
    visited.clear();
  }
  const std::unordered_set<std::string>* active_set =
      (null_checker || has_inline_list) ? &inline_random : nullptr;
  bool solved = RandomizeObject(obj, ctx, arena, expr, expr->inline_constraint,
                                active_set, null_checker, visited);
  out = MakeLogic4VecVal(arena, 32, solved ? 1 : 0);
  return true;
}

namespace {

// 18.12: recognize the scope randomize function. It is spelled
// std::randomize(), or -- outside a class method, where a bare `randomize`
// would instead name the class's own built-in method -- simply randomize(). The
// parser leaves the callee as a plain identifier for the bare form and as a
// `std::randomize` member access for the qualified form.
bool IsScopeRandomizeForm(const Expr* expr, SimContext& ctx) {
  if (expr == nullptr || expr->kind != ExprKind::kCall || expr->lhs == nullptr)
    return false;
  const Expr* callee = expr->lhs;
  if (callee->kind == ExprKind::kMemberAccess && callee->rhs != nullptr &&
      callee->rhs->kind == ExprKind::kIdentifier &&
      callee->rhs->text == "randomize" && callee->lhs != nullptr &&
      callee->lhs->kind == ExprKind::kIdentifier && callee->lhs->text == "std")
    return true;
  if (callee->kind == ExprKind::kIdentifier && callee->text == "randomize" &&
      ctx.CurrentMethodClass() == nullptr && ctx.CurrentThis() == nullptr)
    return true;
  return false;
}

}  // namespace

bool TryEvalScopeRandomizeCall(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  if (!IsScopeRandomizeForm(expr, ctx)) return false;

  // 18.12: the arguments specify the variables of the current scope that are to
  // be assigned random values. Resolve each to a live scope variable; a
  // non-identifier argument is not a form this scope randomize path services,
  // so defer to ordinary dispatch rather than misfire.
  std::vector<Variable*> targets;
  std::vector<std::string> names;
  for (const Expr* arg : expr->args) {
    if (arg == nullptr || arg->kind != ExprKind::kIdentifier) return false;
    Variable* var = ctx.FindVariable(arg->text);
    if (var == nullptr) return false;
    targets.push_back(var);
    names.emplace_back(arg->text);
  }

  // 18.12: called with no argument, the scope randomize does not change the
  // value of any variable and instead checks its constraints, returning 1 when
  // all of them hold. Without a with constraint_block (that form is 18.12.1)
  // there is no constraint expression to evaluate to false, so the checker
  // takes the "otherwise" branch and returns 1, leaving every variable
  // untouched.
  if (targets.empty()) {
    out = MakeLogic4VecVal(arena, 32, 1);
    return true;
  }

  // 18.12: the scope randomize behaves exactly as a class randomize method,
  // only over the current scope's variables. Seed from the active per-process
  // generator so the draw is fresh and thread-stable (18.14.2). Each named
  // variable is a rand variable whose domain spans its declared width, and its
  // current value is seeded so a failed solve can leave it unchanged.
  ConstraintSolver solver(static_cast<uint32_t>(ctx.ActiveRng()()));
  for (size_t i = 0; i < targets.size(); ++i) {
    uint32_t w = targets[i]->value.width;
    if (w == 0) w = 32;
    RandVariable rv;
    rv.name = names[i];
    rv.width = w;
    rv.min_val = 0;
    rv.max_val = (w >= 63) ? INT64_MAX : ((int64_t{1} << w) - 1);
    rv.value = static_cast<int64_t>(targets[i]->value.ToUint64());
    solver.AddVariable(rv);
  }

  bool ok = solver.SolveWith({});

  // 18.12: the call returns 1 only when it successfully sets all the random
  // variables to valid values, in which case each drawn value is written back;
  // otherwise it returns 0. 18.6.3: on failure the variables retain their
  // previous values, so nothing is written back.
  if (ok) {
    for (size_t i = 0; i < targets.size(); ++i) {
      uint32_t w = targets[i]->value.width;
      if (w == 0) w = 32;
      targets[i]->value = MakeLogic4VecVal(
          arena, w, static_cast<uint64_t>(solver.GetValue(names[i])));
    }
  }
  out = MakeLogic4VecVal(arena, 32, ok ? 1 : 0);
  return true;
}

bool TryEvalObjectSrandom(const Expr* expr, SimContext& ctx, Arena& arena,
                          Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.method_name != "srandom") return false;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // §18.13.3: srandom() seeds the object's own RNG with the given seed. The
  // argument is an int, so evaluate it and narrow to the 32-bit seed. Resetting
  // the object's stream here makes a following randomize() replay the sequence
  // keyed by `seed` (§18.14 object stability).
  uint32_t seed = 0;
  if (!expr->args.empty()) {
    seed =
        static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  }
  ctx.SeedObjectRng(obj, seed);
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

bool TryEvalObjectGetRandState(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.method_name != "get_randstate") return false;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // §18.13.4: return the object's current RNG state as a string. The state is
  // of implementation-dependent length and format; here it is the mt19937
  // serialization, packed so it round-trips through a string-typed variable and
  // back into set_randstate().
  out = StringToLogic4Vec(arena, ctx.GetRandState(obj));
  return true;
}

bool TryEvalObjectSetRandState(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.method_name != "set_randstate") return false;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // §18.13.5: install the given string as the object's RNG internal state,
  // overwriting whatever the generator held. The argument is a string, so read
  // its raw bytes back before handing it to the deserializer. set_randstate()
  // returns void.
  std::string state;
  if (!expr->args.empty()) {
    state = Logic4VecToString(EvalExpr(expr->args[0], ctx, arena));
  }
  ctx.SetRandState(obj, state);
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

bool TryEvalObjectConstraintMode(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  std::string_view obj_name;
  std::string_view constraint_name;
  if (!ExtractConstraintModeParts(expr, obj_name, constraint_name))
    return false;
  MethodCallParts parts;
  parts.var_name = obj_name;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // 18.9 nonvoid form: called with no argument, constraint_mode() returns the
  // current active state of the named block -- 1 (ON) when active, 0 (OFF) when
  // inactive.
  if (expr->args.empty()) {
    bool active = IsObjectConstraintActive(obj, constraint_name);
    out = MakeLogic4VecVal(arena, 32, active ? 1 : 0);
    return true;
  }

  // 18.9 / Table 18-4 void form: the argument selects ON (nonzero) or OFF
  // (zero). A named call sets that one block; a call with no constraint
  // identifier applies to every constraint block in the object's class
  // hierarchy.
  bool on = EvalExpr(expr->args[0], ctx, arena).ToUint64() != 0;
  if (constraint_name.empty()) {
    for (const auto* lvl = obj->type; lvl != nullptr; lvl = lvl->parent) {
      if (!lvl->decl) continue;
      for (const ClassMember* m : lvl->decl->members) {
        if (m->kind == ClassMemberKind::kConstraint)
          SetObjectConstraintActive(obj, m->name, on);
      }
    }
  } else {
    SetObjectConstraintActive(obj, constraint_name, on);
  }
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

bool TryEvalObjectRandMode(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  std::string_view obj_name;
  std::string_view var_name;
  if (!ExtractRandModeParts(expr, obj_name, var_name)) return false;
  MethodCallParts parts;
  parts.var_name = obj_name;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // 18.8 nonvoid form: called with no argument, rand_mode() returns the current
  // active state of the named variable -- 1 (ON) when active, 0 (OFF) when
  // inactive. This form must name a variable; a no-name query matches neither
  // form, so leave it for normal dispatch.
  if (expr->args.empty()) {
    if (var_name.empty()) return false;
    bool active = IsObjectRandActive(obj, var_name);
    out = MakeLogic4VecVal(arena, 32, active ? 1 : 0);
    return true;
  }

  // 18.8 / Table 18-3 void form: the argument selects ON (nonzero) or OFF
  // (zero). A named call sets that one variable; a call with no variable name
  // applies to every rand/randc variable in the object's class hierarchy.
  bool on = EvalExpr(expr->args[0], ctx, arena).ToUint64() != 0;
  if (var_name.empty()) {
    for (const auto* lvl = obj->type; lvl != nullptr; lvl = lvl->parent) {
      if (!lvl->decl) continue;
      for (const ClassMember* m : lvl->decl->members) {
        if (m->kind == ClassMemberKind::kProperty &&
            (m->is_rand || m->is_randc))
          SetObjectRandActive(obj, m->name, on);
      }
    }
  } else {
    SetObjectRandActive(obj, var_name, on);
  }
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

}  // namespace delta
