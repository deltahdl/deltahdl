#include "elaborator/type_ref_walks.h"

#include <algorithm>
#include <cstddef>
#include <functional>
#include <optional>
#include <span>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/assertion_body_slots.h"
#include "elaborator/assoc_index_type.h"
#include "elaborator/covergroup_expr_slots.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/let_construct.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_ref_dynamic_element.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/parser_data_decl_internal.h"

namespace delta {

namespace {

void ResolveLocalTypeRef(DataType& dt, std::vector<Expr*>& unpacked_dims,
                         SourceLoc loc,
                         const std::vector<ProceduralLocal>& locals,
                         const TypeRefResolver& resolve_outer);

void ResolveArgumentTypeRef(DataType& arg, SourceLoc loc,
                            const std::vector<ProceduralLocal>& locals,
                            const TypeRefResolver& resolve_outer) {
  std::vector<Expr*> taken_dims;
  ResolveLocalTypeRef(arg, taken_dims, loc, locals, resolve_outer);
  if (!taken_dims.empty()) arg.operand_unpacked_dims = std::move(taken_dims);
}

void ResolveLocalTypeRef(DataType& dt, std::vector<Expr*>& unpacked_dims,
                         SourceLoc loc,
                         const std::vector<ProceduralLocal>& locals,
                         const TypeRefResolver& resolve_outer) {
  ResolveTypeRefArguments(dt.type_params, [&](DataType& arg) {
    ResolveArgumentTypeRef(arg, loc, locals, resolve_outer);
  });
  if (dt.type_ref_expr == nullptr) return;
  const Expr* operand = TypeRefOperand(dt.type_ref_expr);
  auto local = std::find_if(
      locals.rbegin(), locals.rend(), [&](const ProceduralLocal& l) {
        return operand != nullptr && operand->kind == ExprKind::kIdentifier &&
               l.name == operand->text;
      });
  const std::vector<Expr*> kTaken = local == locals.rend()
                                        ? resolve_outer(dt, loc, locals)
                                        : *local->unpacked_dims;
  if (local != locals.rend()) dt = *local->type;
  unpacked_dims.insert(unpacked_dims.end(), kTaken.begin(), kTaken.end());
}

void DeclareForLoopLocals(Stmt* s, std::vector<ProceduralLocal>& locals,
                          const TypeRefResolver& resolve_outer) {
  if (s->kind != StmtKind::kFor) return;
  static const std::vector<Expr*> kNoUnpackedDims;
  const size_t kCount = std::min(s->for_inits.size(), s->for_init_types.size());
  for (size_t k = 0; k < kCount; ++k) {
    DataType& type = s->for_init_types[k];
    std::vector<Expr*> taken_dims;
    ResolveLocalTypeRef(type, taken_dims, s->range.start, locals,
                        resolve_outer);
    if (type.kind == DataTypeKind::kImplicit) continue;
    locals.push_back(
        {ExprIdent(s->for_inits[k]->lhs), &type, &kNoUnpackedDims});
  }
}

void ResolveLocalIndexTypeRefs(std::vector<Expr*>& dims, SourceLoc loc,
                               const std::vector<ProceduralLocal>& locals,
                               const TypeRefResolver& resolve_outer,
                               Arena& arena) {
  ResolveTypeRefIndexDims(
      dims,
      [&](DataType& type) {
        std::vector<Expr*> taken_dims;
        ResolveLocalTypeRef(type, taken_dims, loc, locals, resolve_outer);
      },
      arena);
}

void ResolvePrefixArguments(Expr& prefix,
                            const std::function<void(DataType&)>& resolve,
                            Arena& arena) {
  for (Expr*& element : prefix.elements) {
    if (element == nullptr || element->kind != ExprKind::kTypeRef) continue;
    std::vector<DataType> args(1);
    args.front().type_ref_expr = element;
    ResolveTypeRefArguments(args, resolve);
    if (args.front().type_ref_expr != nullptr) continue;
    auto* resolved = arena.Create<Expr>(*element);
    resolved->lhs = nullptr;
    resolved->type_value = arena.Create<DataType>(args.front());
    element = resolved;
  }
}

void ResolveConstraintPrefixTypeRefs(const ClassMember& block, SourceLoc loc,
                                     const std::vector<ProceduralLocal>& locals,
                                     const TypeRefResolver& resolve,
                                     Arena& arena);

TypeRefResolver ResolverInRandomizedObject(
    const Expr& call, const std::vector<ProceduralLocal>& locals,
    const TypeRefResolver& resolve_outer, Arena& arena);

void ResolvePrefixTypeRefs(const Expr* e, SourceLoc loc,
                           const std::vector<ProceduralLocal>& locals,
                           const TypeRefResolver& resolve_outer, Arena& arena) {
  if (e == nullptr) return;
  if (e->has_param_spec) {
    ResolvePrefixArguments(
        *const_cast<Expr*>(e),
        [&](DataType& arg) {
          std::vector<Expr*> taken_dims;
          ResolveLocalTypeRef(arg, taken_dims, loc, locals, resolve_outer);
        },
        arena);
  }
  auto in_expr = [&](const Expr* sub) {
    ResolvePrefixTypeRefs(sub, loc, locals, resolve_outer, arena);
  };
  ForEachExprChild(e, in_expr);
  if (e->property_actual != nullptr)
    ForEachTreeSlot(e->property_actual, in_expr);
  if (e->inline_constraint != nullptr) {
    ResolveConstraintPrefixTypeRefs(
        *e->inline_constraint, loc, {},
        ResolverInRandomizedObject(*e, locals, resolve_outer, arena), arena);
  }
}

void ForEachDistExpr(const std::vector<ConstraintDistRef>& refs,
                     const std::function<void(const Expr*)>& fn) {
  for (const ConstraintDistRef& ref : refs) {
    fn(ref.target);
    for (const ConstraintDistItem& item : ref.items) {
      for (const Expr* e :
           {item.value, item.lo, item.hi, item.tolerance, item.weight}) {
        fn(e);
      }
    }
  }
}

void ResolveConstraintPrefixTypeRefs(const ClassMember& block, SourceLoc loc,
                                     const std::vector<ProceduralLocal>& locals,
                                     const TypeRefResolver& resolve,
                                     Arena& arena) {
  static const DataType kLoopVariable = [] {
    DataType type;
    type.kind = DataTypeKind::kInt;
    type.is_signed = true;
    return type;
  }();
  static const std::vector<Expr*> kNoUnpackedDims;
  auto in_expr = [&](const Expr* e) {
    ResolvePrefixTypeRefs(e, loc, locals, resolve, arena);
  };
  for (const ConstraintForeachRef& ref : block.constraint_foreach_refs) {
    std::vector<ProceduralLocal> in_loop = locals;
    in_loop.reserve(locals.size() + ref.loop_vars.size());
    for (std::string_view name : ref.loop_vars)
      in_loop.push_back({name, &kLoopVariable, &kNoUnpackedDims});
    for (const Expr* e : ref.body)
      ResolvePrefixTypeRefs(e, ref.loc, in_loop, resolve, arena);
  }
  for (const auto* exprs :
       {&block.constraint_exprs, &block.constraint_soft_exprs}) {
    for (const Expr* e : *exprs) in_expr(e);
  }
  ForEachDistExpr(block.constraint_dist_refs, in_expr);
  ForEachDistExpr(block.constraint_soft_dist_refs, in_expr);
}

void ResolveStmtPrefixTypeRefs(Stmt* s,
                               const std::vector<ProceduralLocal>& locals,
                               const TypeRefResolver& resolve_outer,
                               Arena& arena) {
  auto in_expr = [&](const Expr* e) {
    ResolvePrefixTypeRefs(e, s->range.start, locals, resolve_outer, arena);
  };
  ForEachChildExpr(s, in_expr);
  in_expr(s->assert_disable_iff);
  ForEachEventSlot(s->assert_clock, in_expr);
  if (s->assert_sequence != nullptr)
    ForEachBodySlot(s->assert_sequence->seq_linear, in_expr);
  if (s->assert_property != nullptr)
    ForEachTreeSlot(s->assert_property, in_expr);
}

const DataType* UntypedFormal(std::string_view name, Arena& arena) {
  auto* type = arena.Create<DataType>();
  auto* operand = arena.Create<Expr>();
  operand->kind = ExprKind::kIdentifier;
  operand->text = name;
  type->type_ref_expr = operand;
  return type;
}

const DataType* AssertionLocalType(const SeqLocalDecl& local, Arena& arena) {
  auto* type = arena.Create<DataType>(local.named_type);
  if (type->kind == DataTypeKind::kImplicit) {
    type->kind =
        TokenToTypeKind(local.type_kw).value_or(DataTypeKind::kImplicit);
    type->is_signed = local.signing == TokenKind::kEof
                          ? IsImplicitlySigned(type->kind)
                          : local.signing == TokenKind::kKwSigned;
  }
  if (!local.packed_dims.empty()) {
    type->packed_dim_left = local.packed_dims.front().first;
    type->packed_dim_right = local.packed_dims.front().second;
    type->extra_packed_dims.assign(local.packed_dims.begin() + 1,
                                   local.packed_dims.end());
  }
  return type;
}

std::vector<ProceduralLocal> NamesOfAssertionDecl(const ModuleItem& decl,
                                                  Arena& arena) {
  static const std::vector<Expr*> kNoUnpackedDims;
  std::vector<ProceduralLocal> names;
  for (size_t i = 0; i < decl.prop_formals.size(); ++i) {
    const std::string_view kName = decl.prop_formals[i];
    const DataType* type = decl.prop_formal_types[i];
    if (type == nullptr) type = UntypedFormal(kName, arena);
    names.push_back({kName, type, &decl.prop_formal_unpacked_dims[i]});
  }
  for (const auto* locals : {&decl.prop_locals, &decl.seq_linear.locals}) {
    for (const SeqLocalDecl& local : *locals) {
      names.push_back(
          {local.name, AssertionLocalType(local, arena), &kNoUnpackedDims});
    }
  }
  return names;
}

void ResolveAssertionDeclPrefixTypeRefs(ModuleItem& decl,
                                        const TypeRefResolver& resolve,
                                        Arena& arena) {
  const std::vector<ProceduralLocal> kNames = NamesOfAssertionDecl(decl, arena);
  auto in_expr = [&](const Expr* e) {
    ResolvePrefixTypeRefs(e, decl.loc, kNames, resolve, arena);
  };
  in_expr(decl.prop_body_expr);
  in_expr(decl.prop_disable_iff);
  for (const Expr* actual : decl.prop_formal_defaults) in_expr(actual);
  for (const SeqLocalDecl& local : decl.prop_locals) in_expr(local.init);
  ForEachEventSlot(decl.prop_clock, in_expr);
  ForEachEventSlot(decl.seq_clock, in_expr);
  ForEachBodySlot(decl.seq_linear, in_expr);
  if (decl.prop_body_tree != nullptr)
    ForEachTreeSlot(decl.prop_body_tree, in_expr);
}

static std::vector<bool> UntypedLetFormals(const ModuleItem& item) {
  std::vector<bool> untyped(item.func_args.size(), false);
  if (item.kind != ModuleItemKind::kLetDecl) return untyped;
  const std::vector<const DataType*> kTypes = LetFormalTypes(item.func_args);
  for (size_t i = 0; i < untyped.size(); ++i) {
    untyped[i] = kTypes[i] == nullptr &&
                 item.func_args[i].data_type.type_ref_expr == nullptr;
  }
  return untyped;
}

void ResolveFormalTypeRefs(ModuleItem* item,
                           std::vector<ProceduralLocal>& locals,
                           const TypeRefResolver& resolve_outer, Arena& arena) {
  const std::vector<bool> kUntyped = UntypedLetFormals(*item);
  for (size_t i = 0; i < item->func_args.size(); ++i) {
    FunctionArg& arg = item->func_args[i];
    ResolvePrefixTypeRefs(arg.data_type.type_ref_expr, item->loc, locals,
                          resolve_outer, arena);
    ResolveLocalTypeRef(arg.data_type, arg.unpacked_dims, item->loc, locals,
                        resolve_outer);
    ResolveLocalIndexTypeRefs(arg.unpacked_dims, item->loc, locals,
                              resolve_outer, arena);
    ResolvePrefixTypeRefs(arg.default_value, item->loc, locals, resolve_outer,
                          arena);
    locals.push_back(
        {arg.name,
         kUntyped[i] ? UntypedFormal(arg.name, arena) : &arg.data_type,
         &arg.unpacked_dims});
  }
}

void ResolveTypedefTypeRef(ModuleItem& item,
                           const std::vector<ProceduralLocal>& locals,
                           const TypeRefResolver& resolve, Arena& arena) {
  ResolveLocalTypeRef(item.typedef_type, item.unpacked_dims, item.loc, locals,
                      resolve);
  ResolveLocalIndexTypeRefs(item.unpacked_dims, item.loc, locals, resolve,
                            arena);
}

void ResolveTypeRefsInStmt(Stmt* s, std::vector<ProceduralLocal>& locals,
                           const TypeRefResolver& resolve_outer, Arena& arena,
                           const ProceduralStmtVisitor& visit) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlockItemDecl &&
      s->decl_item->kind == ModuleItemKind::kLetDecl) {
    std::vector<ProceduralLocal> in_let = locals;
    ResolveFormalTypeRefs(s->decl_item, in_let, resolve_outer, arena);
    ResolvePrefixTypeRefs(s->decl_item->init_expr, s->decl_item->loc, in_let,
                          resolve_outer, arena);
    return;
  }
  if (s->kind == StmtKind::kBlockItemDecl &&
      s->decl_item->kind == ModuleItemKind::kTypedef) {
    ResolveTypedefTypeRef(*s->decl_item, locals, resolve_outer, arena);
    return;
  }
  if (s->kind != StmtKind::kVarDecl) {
    const size_t kOuter = locals.size();
    DeclareForLoopLocals(s, locals, resolve_outer);
    ResolveStmtPrefixTypeRefs(s, locals, resolve_outer, arena);
    if (visit) visit(s, locals);
    ForEachChildStmt(s, [&](Stmt* const& sub) {
      ResolveTypeRefsInStmt(sub, locals, resolve_outer, arena, visit);
    });
    locals.resize(kOuter);
    return;
  }
  ResolvePrefixTypeRefs(s->var_decl_type.type_ref_expr, s->range.start, locals,
                        resolve_outer, arena);
  ResolveLocalTypeRef(s->var_decl_type, s->var_unpacked_dims, s->range.start,
                      locals, resolve_outer);
  ResolveLocalIndexTypeRefs(s->var_unpacked_dims, s->range.start, locals,
                            resolve_outer, arena);
  ResolveStmtPrefixTypeRefs(s, locals, resolve_outer, arena);
  if (visit) visit(s, locals);
  locals.push_back({s->var_name, &s->var_decl_type, &s->var_unpacked_dims});
}

const Expr* PropertyName(const Expr& ref) {
  const Expr* name = &ref;
  if (ref.kind == ExprKind::kMemberAccess && !ref.is_scope_resolution &&
      ref.lhs != nullptr && ref.lhs->kind == ExprKind::kIdentifier &&
      ref.lhs->text == "this") {
    name = ref.rhs;
  }
  if (name == nullptr || name->kind != ExprKind::kIdentifier) return nullptr;
  return name;
}

const ClassMember* PropertyNamed(const ClassDecl& cls, const Expr& ref,
                                 const CompilationUnit* unit) {
  const Expr* name = PropertyName(ref);
  if (name == nullptr) return nullptr;
  OwnedMember owned;
  if (unit != nullptr) {
    owned = FindMemberAndOwner(&cls, name->text, unit);
  } else {
    auto own = std::ranges::find_if(cls.members, [&](const ClassMember* m) {
      return m->name == name->text;
    });
    if (own != cls.members.end()) owned = {*own, &cls};
  }
  if (owned.member == nullptr ||
      owned.member->kind != ClassMemberKind::kProperty) {
    return nullptr;
  }
  if (owned.owner != &cls && !owned.owner->params.empty()) return nullptr;
  return owned.member;
}

std::vector<ProceduralLocal> PropertiesInScope(const ClassDecl& cls,
                                               const CompilationUnit& unit) {
  std::vector<const ClassDecl*> chain = {&cls};
  while (!chain.back()->base_class.empty()) {
    const ClassDecl* base = FindBaseClass(chain.back(), &unit);
    if (base == nullptr || !base->params.empty()) break;
    chain.push_back(base);
  }
  std::vector<ProceduralLocal> properties;
  for (auto c = chain.rbegin(); c != chain.rend(); ++c) {
    for (const ClassMember* m : (*c)->members) {
      if (m->kind == ClassMemberKind::kProperty)
        properties.push_back({m->name, &m->data_type, &m->unpacked_dims});
    }
  }
  return properties;
}

std::vector<ProceduralLocal> SelfHandles(const ClassDecl& cls, Arena& arena) {
  static const std::vector<Expr*> kNoUnpackedDims;
  auto* self = arena.Create<DataType>();
  self->kind = DataTypeKind::kNamed;
  self->type_name = cls.name;
  std::vector<ProceduralLocal> handles = {{"this", self, &kNoUnpackedDims}};
  if (cls.base_class.empty()) return handles;
  auto* base = arena.Create<DataType>();
  base->kind = DataTypeKind::kNamed;
  base->type_name = cls.base_class;
  base->scope_name = cls.base_class_scope;
  base->type_params = cls.base_class_type_params;
  handles.push_back({"super", base, &kNoUnpackedDims});
  return handles;
}

std::vector<ProceduralLocal> NamesInScope(
    std::span<const ProceduralLocal> outer,
    std::span<const ProceduralLocal> inner) {
  std::vector<ProceduralLocal> all(outer.begin(), outer.end());
  all.insert(all.end(), inner.begin(), inner.end());
  return all;
}

const Expr* RandomizedObject(const Expr& call, Arena& arena) {
  const Expr* name = call.lhs;
  if (name->kind == ExprKind::kMemberAccess)
    return name->is_scope_resolution ? nullptr : name->lhs;
  auto* self = arena.Create<Expr>();
  self->kind = ExprKind::kIdentifier;
  self->text = "this";
  self->range = name->range;
  return self;
}

Expr* LocalQualifiedName(const Expr& operand) {
  if (operand.kind != ExprKind::kMemberAccess || !operand.is_scope_resolution ||
      operand.lhs->text != "local") {
    return nullptr;
  }
  return operand.rhs;
}

const Expr* ObjectMemberName(const Expr& operand, const Expr& call) {
  const Expr* name = PropertyName(operand);
  if (name == &operand && call.with_has_parens &&
      !std::ranges::contains(call.with_restrict_ids, name->text)) {
    return nullptr;
  }
  return name;
}

Expr* ObjectMemberAccess(const Expr& object, const Expr& name, Arena& arena) {
  auto* access = arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = const_cast<Expr*>(&object);
  access->rhs = const_cast<Expr*>(&name);
  access->range = name.range;
  return access;
}

Expr* ObjectMemberProbe(const Expr& object, const Expr& name, Arena& arena) {
  Expr* access = ObjectMemberAccess(object, name, arena);
  access->asks_for_object_member = true;
  return access;
}

struct ObjectOperandRewrite {
  const Expr& call;
  const Expr& object;
  SourceLoc loc;
  std::span<const ProceduralLocal> names;
  const TypeRefResolver& resolve_outer;
  Arena& arena;
  bool changed = false;

  bool NamesObjectMember(const Expr& name) const {
    DataType probe;
    probe.type_ref_expr = ObjectMemberProbe(object, name, arena);
    resolve_outer(probe, loc, names);
    return probe.type_ref_expr == nullptr;
  }

  Expr* Leaf(Expr* name) {
    const bool kSelf = name->text == "this";
    if (!kSelf &&
        (!name->scope_prefix.empty() ||
         ObjectMemberName(*name, call) == nullptr || !NamesObjectMember(*name)))
      return name;
    changed = true;
    return kSelf ? const_cast<Expr*>(&object)
                 : ObjectMemberAccess(object, *name, arena);
  }

  Expr* Rewrite(Expr* e) {
    if (e == nullptr) return nullptr;
    if (e->kind == ExprKind::kIdentifier) return Leaf(e);
    if (e->kind == ExprKind::kMemberAccess && e->is_scope_resolution) return e;
    auto* copy = arena.Create<Expr>(*e);
    copy->lhs = Rewrite(e->lhs);
    if (e->kind == ExprKind::kMemberAccess) return copy;
    for (Expr** slot :
         {&copy->rhs, &copy->condition, &copy->true_expr, &copy->false_expr,
          &copy->base, &copy->index, &copy->index_end})
      *slot = Rewrite(*slot);
    for (auto& sub : copy->elements) sub = Rewrite(sub);
    for (auto& sub : copy->args) sub = Rewrite(sub);
    return copy;
  }
};

std::optional<std::vector<Expr*>> ResolveObjectOperand(
    DataType& dt, const Expr& operand, ObjectOperandRewrite rewrite) {
  Expr* rewritten = rewrite.Rewrite(const_cast<Expr*>(&operand));
  if (!rewrite.changed) return std::nullopt;
  DataType whole = dt;
  whole.type_ref_expr = rewritten;
  std::vector<Expr*> dims =
      rewrite.resolve_outer(whole, rewrite.loc, rewrite.names);
  dt = whole;
  return dims;
}

TypeRefResolver ResolverInRandomizedObject(
    const Expr& call, const std::vector<ProceduralLocal>& locals,
    const TypeRefResolver& resolve_outer, Arena& arena) {
  const Expr* object = RandomizedObject(call, arena);
  return [&call, &locals, &resolve_outer, &arena, object](
             DataType& dt, SourceLoc loc,
             std::span<const ProceduralLocal> inner) {
    const std::vector<ProceduralLocal> kNames = NamesInScope(locals, inner);
    const Expr* operand = TypeRefOperand(dt.type_ref_expr);
    std::vector<Expr*> dims;
    const Expr* member =
        object == nullptr ? nullptr : ObjectMemberName(*operand, call);
    if (Expr* local = LocalQualifiedName(*operand)) {
      dt.type_ref_expr = local;
    } else if (member != nullptr) {
      DataType probe = dt;
      probe.type_ref_expr = ObjectMemberProbe(*object, *member, arena);
      dims = resolve_outer(probe, loc, kNames);
      if (probe.type_ref_expr == nullptr) {
        dt = probe;
        return dims;
      }
      if (probe.type_ref_expr->asks_for_object_member) return dims;
    } else if (object != nullptr) {
      if (std::optional<std::vector<Expr*>> taken = ResolveObjectOperand(
              dt, *operand, {call, *object, loc, kNames, resolve_outer, arena}))
        return *taken;
    }
    ResolveLocalTypeRef(dt, dims, loc, kNames, resolve_outer);
    return dims;
  };
}

void ResolveItemIndexTypeRefs(ModuleItem& item, const TypeRefResolver& resolve,
                              Arena& arena) {
  ResolveTypeRefIndexDims(
      item.unpacked_dims, [&](DataType& type) { resolve(type, item.loc, {}); },
      arena);
}

void ResolveItemArgumentTypeRefs(ModuleItem& item,
                                 const TypeRefResolver& resolve) {
  ResolveTypeRefArguments(item.data_type.type_params, [&](DataType& arg) {
    std::vector<Expr*> taken_dims;
    ResolveLocalTypeRef(arg, taken_dims, item.loc, {}, resolve);
  });
}

void ResolveCovergroupPrefixTypeRefs(const CovergroupDecl& group, SourceLoc loc,
                                     const TypeRefResolver& resolve,
                                     Arena& arena) {
  for (const FunctionArg& formal : group.formals)
    ResolvePrefixTypeRefs(formal.default_value, loc, {}, resolve, arena);
  std::vector<ProceduralLocal> formals;
  formals.reserve(group.formals.size() + group.event.sample_formals.size());
  for (const auto* list : {&group.formals, &group.event.sample_formals}) {
    for (const FunctionArg& formal : *list)
      formals.push_back(
          {formal.name, &formal.data_type, &formal.unpacked_dims});
  }
  auto in_expr = [&](const Expr* e) {
    ResolvePrefixTypeRefs(e, loc, formals, resolve, arena);
  };
  ForEachCovergroupExpr(group, in_expr);
}

void ResolveScopeItemTypeRefs(const std::vector<ModuleItem*>& items,
                              const TypeRefResolver& resolve,
                              const CompilationUnit* unit, Arena& arena,
                              const ProceduralStmtVisitor& visit) {
  for (ModuleItem* item : items) {
    switch (item->kind) {
      case ModuleItemKind::kTypedef:
        ResolveTypedefTypeRef(*item, {}, resolve, arena);
        break;
      case ModuleItemKind::kNettypeDecl:
        resolve(item->typedef_type, item->loc, {});
        break;
      case ModuleItemKind::kVarDecl:
        ResolveItemArgumentTypeRefs(*item, resolve);
        ResolveItemIndexTypeRefs(*item, resolve, arena);
        break;
      case ModuleItemKind::kFunctionDecl:
      case ModuleItemKind::kTaskDecl:
      case ModuleItemKind::kLetDecl:
        ResolveProceduralTypeRefs(item, resolve, arena, visit);
        break;
      case ModuleItemKind::kClassDecl:
        ResolveClassTypeRefs(*item->class_decl, resolve, unit, arena, visit);
        break;
      case ModuleItemKind::kCovergroupDecl:
        ResolveCovergroupPrefixTypeRefs(*item->covergroup, item->loc, resolve,
                                        arena);
        break;
      default:
        break;
    }
  }
}

void ForEachItemTypeRef(
    const std::vector<ModuleItem*>& items,
    const std::function<void(const Expr*, SourceLoc)>& on_ref) {
  for (const ModuleItem* item : items) {
    if ((item->kind == ModuleItemKind::kVarDecl ||
         item->kind == ModuleItemKind::kNetDecl) &&
        item->data_type.type_ref_expr != nullptr) {
      on_ref(item->data_type.type_ref_expr, item->loc);
    }
    ForEachItemExprTypeRef(item, on_ref);
  }
}

}  // namespace

void ResolveProceduralTypeRefs(ModuleItem* item,
                               const TypeRefResolver& resolve_outer,
                               Arena& arena,
                               const ProceduralStmtVisitor& visit) {
  std::vector<ProceduralLocal> locals;
  locals.reserve(item->func_args.size());
  ResolveFormalTypeRefs(item, locals, resolve_outer, arena);
  ResolveLocalTypeRef(item->return_type, item->return_array_dims, item->loc,
                      locals, resolve_outer);
  if (item->kind == ModuleItemKind::kLetDecl) {
    ResolvePrefixTypeRefs(item->init_expr, item->loc, locals, resolve_outer,
                          arena);
  }
  ResolveTypeRefsInStmt(item->body, locals, resolve_outer, arena, visit);
  for (auto* s : item->func_body_stmts) {
    ResolveTypeRefsInStmt(s, locals, resolve_outer, arena, visit);
  }
}

void ResolveItemPrefixTypeRefs(ModuleItem& item, const TypeRefResolver& resolve,
                               Arena& arena) {
  if (item.kind == ModuleItemKind::kLetDecl) return;
  ResolveAssertionDeclPrefixTypeRefs(item, resolve, arena);
  for (ModuleItem* decl : item.clocking_decls)
    ResolveAssertionDeclPrefixTypeRefs(*decl, resolve, arena);
  auto in_expr = [&](const Expr* e) {
    ResolvePrefixTypeRefs(e, item.loc, {}, resolve, arena);
  };
  for (const Expr* e :
       {item.data_type.type_ref_expr, item.init_expr, item.assign_lhs,
        item.assign_rhs, item.assign_delay, item.assign_delay_fall,
        item.assign_delay_decay, item.net_delay, item.net_delay_fall,
        item.net_delay_decay, item.gate_delay, item.gate_delay_fall,
        item.gate_delay_decay}) {
    in_expr(e);
  }
  in_expr(item.assert_expr);
  ForEachEventSlot(item.sensitivity, in_expr);
  ForEachEventSlot(item.clocking_event, in_expr);
  for (const Expr* terminal : item.gate_terminals) in_expr(terminal);
  for (const auto& [port, actual] : item.inst_ports) in_expr(actual);
  if (item.covergroup != nullptr)
    ResolveCovergroupPrefixTypeRefs(*item.covergroup, item.loc, resolve, arena);
}

static bool HeaderRefersToAType(const ClassDecl& cls) {
  return std::ranges::any_of(cls.param_types, [](const DataType& type) {
    return type.type_ref_expr != nullptr;
  });
}

static const std::vector<Expr*>* HeaderUnpackedDims(const ClassDecl& cls,
                                                    std::string_view name) {
  static const std::vector<Expr*> kNone;
  const auto kDims = cls.param_port_unpacked_dims.find(name);
  return kDims == cls.param_port_unpacked_dims.end() ? &kNone : &kDims->second;
}

static std::vector<ProceduralLocal> ResolveHeaderTypeRefs(
    ClassDecl& cls, const TypeRefResolver& resolve_outer, Arena& arena) {
  std::vector<ProceduralLocal> values;
  const bool kRefers = HeaderRefersToAType(cls);
  for (size_t i = 0; i < cls.params.size(); ++i) {
    const auto& [name, value] = cls.params[i];
    const SourceLoc kLoc = cls.param_port_locs[i];
    auto resolve_header_type = [&](DataType& type) {
      if (type.type_ref_expr != nullptr) resolve_outer(type, kLoc, values);
    };
    if (cls.type_param_names.contains(name)) {
      resolve_header_type(cls.param_types[i]);
      continue;
    }
    DataType* type = &cls.param_types[i];
    if (type->kind == DataTypeKind::kImplicit) {
      if (!kRefers) continue;
      type = arena.Create<DataType>(*type);
      if (type->type_ref_expr == nullptr) type->type_ref_expr = value;
      resolve_header_type(*type);
    }
    values.push_back({name, type, HeaderUnpackedDims(cls, name)});
  }
  return values;
}

static std::vector<ProceduralLocal> ResolveClassHeaderTypeRefs(
    ClassDecl& cls, const TypeRefResolver& resolve_outer, Arena& arena) {
  std::vector<ProceduralLocal> values =
      ResolveHeaderTypeRefs(cls, resolve_outer, arena);
  const auto kResolve = [&](DataType& arg) {
    ResolveArgumentTypeRef(arg, cls.range.start, values, resolve_outer);
  };
  ResolveTypeRefArguments(cls.base_class_type_params, kResolve);
  for (auto* refs : {&cls.extends_interfaces, &cls.implements_types}) {
    for (InterfaceRef& ref : *refs)
      ResolveTypeRefArguments(ref.type_params, kResolve);
  }
  return values;
}

namespace {

class ClassTypeRefs {
 public:
  ClassTypeRefs(ClassDecl& cls, const TypeRefResolver& resolve_outer,
                const CompilationUnit* unit, Arena& arena)
      : cls_(cls),
        resolve_outer_(resolve_outer),
        unit_(unit),
        arena_(arena),
        names_(
            NamesInScope(ResolveClassHeaderTypeRefs(cls, resolve_outer, arena),
                         PropertiesInScope(cls, *unit))) {
    names_ = NamesInScope(SelfHandles(cls, arena), names_);
  }

  const std::vector<ProceduralLocal>& Names() const { return names_; }

  std::vector<Expr*> Resolve(DataType& dt, SourceLoc loc,
                             std::span<const ProceduralLocal> locals) const {
    const Expr* operand = TypeRefOperand(dt.type_ref_expr);
    const ClassMember* property =
        operand == nullptr ? nullptr : PropertyNamed(cls_, *operand, unit_);
    if (property == nullptr)
      return resolve_outer_(dt, loc, NamesInScope(names_, locals));
    DataType type = property->data_type;
    std::vector<Expr*> dims = property->unpacked_dims;
    if (type.type_ref_expr != nullptr) {
      const std::vector<Expr*> kTaken = resolve_outer_(type, loc, names_);
      dims.insert(dims.end(), kTaken.begin(), kTaken.end());
    }
    AdoptReferencedType(dt, type);
    return dims;
  }

  void ResolveDeclaration(ClassMember& m, const TypeRefResolver& in_class) {
    if (m.kind == ClassMemberKind::kTypedef) {
      ResolveTypedefTypeRef(*m.typedef_item, {}, in_class, arena_);
      return;
    }
    if (m.kind == ClassMemberKind::kConstraint) {
      ResolveConstraintPrefixTypeRefs(m, m.loc, {}, in_class, arena_);
      return;
    }
    if (m.kind == ClassMemberKind::kCovergroup) {
      ResolveCovergroupPrefixTypeRefs(*m.covergroup, m.loc, in_class, arena_);
      return;
    }
    if (m.kind != ClassMemberKind::kProperty) return;
    ResolveLocalTypeRef(m.data_type, m.unpacked_dims, m.loc, {}, in_class);
    ResolveLocalIndexTypeRefs(m.unpacked_dims, m.loc, {}, in_class, arena_);
    ResolvePrefixTypeRefs(m.init_expr, m.loc, {}, in_class, arena_);
  }

 private:
  ClassDecl& cls_;
  const TypeRefResolver& resolve_outer_;
  const CompilationUnit* unit_;
  Arena& arena_;
  std::vector<ProceduralLocal> names_;
};

}  // namespace

void ResolveClassTypeNames(ClassDecl& cls, const TypeRefResolver& resolve_outer,
                           const CompilationUnit* unit, Arena& arena) {
  ClassTypeRefs refs(cls, resolve_outer, unit, arena);
  const TypeRefResolver kInClass =
      [&](DataType& dt, SourceLoc loc,
          std::span<const ProceduralLocal> locals) {
        return refs.Resolve(dt, loc, locals);
      };
  for (ClassMember* m : cls.members) {
    if (m->kind == ClassMemberKind::kTypedef || cls.params.empty())
      refs.ResolveDeclaration(*m, kInClass);
    if (m->kind == ClassMemberKind::kClassDecl)
      ResolveClassTypeNames(*m->nested_class, kInClass, unit, arena);
  }
}

void ResolveClassTypeRefs(ClassDecl& cls, const TypeRefResolver& resolve_outer,
                          const CompilationUnit* unit, Arena& arena,
                          const ProceduralStmtVisitor& visit) {
  ClassTypeRefs refs(cls, resolve_outer, unit, arena);
  const TypeRefResolver kInClass =
      [&](DataType& dt, SourceLoc loc,
          std::span<const ProceduralLocal> locals) {
        return refs.Resolve(dt, loc, locals);
      };
  ProceduralStmtVisitor in_class;
  if (visit) {
    in_class = [&](Stmt* s, std::span<const ProceduralLocal> locals) {
      visit(s, NamesInScope(refs.Names(), locals));
    };
  }
  for (ClassMember* m : cls.members) {
    switch (m->kind) {
      case ClassMemberKind::kMethod:
        ResolveProceduralTypeRefs(m->method, kInClass, arena, in_class);
        break;
      case ClassMemberKind::kClassDecl:
        ResolveClassTypeRefs(*m->nested_class, kInClass, unit, arena, in_class);
        break;
      default:
        refs.ResolveDeclaration(*m, kInClass);
        break;
    }
  }
}

static void ForEachUnitScope(
    CompilationUnit* unit,
    const std::function<void(const PackageDecl*,
                             const std::vector<ModuleItem*>&)>& on_items,
    const std::function<void(ClassDecl&)>& on_class) {
  for (const PackageDecl* pkg : unit->packages) on_items(pkg, pkg->items);
  on_items(nullptr, unit->cu_items);
  for (ClassDecl* cls : unit->classes) on_class(*cls);
}

void ResolveUnitScopeTypeRefs(CompilationUnit* unit, Arena& arena,
                              std::vector<UnitScopeTypeRef>& written) {
  const PackageDecl* package = nullptr;
  const std::vector<ModuleItem*>* items = nullptr;
  auto record = [&](const Expr* operand, SourceLoc loc,
                    std::span<const ProceduralLocal> locals) {
    written.push_back({operand, loc, package, {locals.begin(), locals.end()}});
  };
  const TypeRefResolver kInScope =
      [&](DataType& dt, SourceLoc loc,
          std::span<const ProceduralLocal> locals) -> std::vector<Expr*> {
    if (dt.type_ref_expr != nullptr) record(dt.type_ref_expr, loc, locals);
    return ResolveScopeTypeRef(dt, *items, arena);
  };
  const ProceduralStmtVisitor kVisit =
      [&](Stmt* s, std::span<const ProceduralLocal> locals) {
        ForEachTypeRefOfStmt(s, [&](const Expr* ref) {
          record(ref->lhs, ref->range.start, locals);
        });
      };
  ForEachUnitScope(
      unit,
      [&](const PackageDecl* pkg, const std::vector<ModuleItem*>& scope_items) {
        package = pkg;
        items = &scope_items;
        ForEachItemTypeRef(scope_items,
                           [&](const Expr* operand, SourceLoc loc) {
                             record(operand, loc, {});
                           });
        ResolveScopeItemTypeRefs(scope_items, kInScope, unit, arena, kVisit);
      },
      [&](ClassDecl& cls) {
        package = nullptr;
        ResolveClassTypeRefs(cls, kInScope, unit, arena, kVisit);
      });
}

void ResolveUnitScopeTypeNames(
    CompilationUnit* unit, Arena& arena,
    const std::function<void(const PackageDecl*)>& enter,
    const TypeRefResolver& resolve) {
  ForEachUnitScope(
      unit,
      [&](const PackageDecl* pkg, const std::vector<ModuleItem*>& items) {
        enter(pkg);
        for (ModuleItem* item : items) {
          if (item->kind == ModuleItemKind::kTypedef) {
            ResolveTypedefTypeRef(*item, {}, resolve, arena);
          } else if (item->kind == ModuleItemKind::kVarDecl) {
            ResolveLocalTypeRef(item->data_type, item->unpacked_dims, item->loc,
                                {}, resolve);
          } else if (item->kind == ModuleItemKind::kClassDecl) {
            ResolveClassTypeNames(*item->class_decl, resolve, unit, arena);
          }
        }
      },
      [&](ClassDecl& cls) {
        enter(nullptr);
        ResolveClassTypeNames(cls, resolve, unit, arena);
      });
}

void ResolveUnitScopeProcedureTypeRefs(
    CompilationUnit* unit, Arena& arena,
    const std::function<void(const PackageDecl*)>& enter,
    const TypeRefResolver& resolve, const ProceduralStmtVisitor& visit) {
  ForEachUnitScope(
      unit,
      [&](const PackageDecl* pkg, const std::vector<ModuleItem*>& items) {
        enter(pkg);
        for (ModuleItem* item : items) {
          if (item->kind == ModuleItemKind::kFunctionDecl ||
              item->kind == ModuleItemKind::kTaskDecl) {
            ResolveProceduralTypeRefs(item, resolve, arena, visit);
          } else if (item->kind == ModuleItemKind::kCovergroupDecl) {
            ResolveCovergroupPrefixTypeRefs(*item->covergroup, item->loc,
                                            resolve, arena);
          } else if (item->kind == ModuleItemKind::kClassDecl &&
                     item->class_decl->params.empty()) {
            ResolveClassTypeRefs(*item->class_decl, resolve, unit, arena,
                                 visit);
          }
        }
      },
      [&](ClassDecl& cls) {
        enter(nullptr);
        if (cls.params.empty())
          ResolveClassTypeRefs(cls, resolve, unit, arena, visit);
      });
}

}  // namespace delta
