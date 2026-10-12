#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// §11.9 takes a tagged union expression's type from the context it stands in.
// This walk carries that context down a module: the declared type of each name
// an assignment may write, the module's functions by name for the formal an
// argument binds to, and the return type of the function whose body is walked.
class TaggedContextWalk {
 public:
  TaggedContextWalk(const TypedefMap& typedefs, DiagEngine& diag)
      : typedefs_(typedefs), diag_(diag) {}

  void Run(const ModuleDecl* decl);

 private:
  const DataType* Resolve(const DataType* type) const;
  const DataType* TypeOfName(const Expr* target) const;
  void CheckTagged(const Expr* e, const DataType* context);
  void CheckTaggedValue(const Expr* e, const StructMember& member);
  void ReportNoMember(const Expr* e, const DataType* context);
  void WalkExpr(const Expr* e);
  void CheckCast(const Expr* e);
  void CheckCallArgs(const Expr* e);
  void WalkStmt(const Stmt* s);
  void CheckAssigned(const Expr* target, const Expr* value);

  const TypedefMap& typedefs_;
  DiagEngine& diag_;
  std::unordered_map<std::string_view, const DataType*> module_types_;
  std::vector<std::pair<std::string_view, const DataType*>> locals_;
  std::unordered_map<std::string_view, const ModuleItem*> functions_;
  const DataType* return_type_ = nullptr;
};

bool IsValueLiteral(const Expr* e) {
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
      return true;
    default:
      return false;
  }
}

// The type a context gives, followed through the typedef table to the type it
// stands for. A name the table holds nothing for -- a class, a type parameter
// -- a type reference, and a chain of names running through one of them twice
// say nothing the walk can judge, and answer nullptr.
const DataType* TaggedContextWalk::Resolve(const DataType* type) const {
  if (type->type_ref_expr != nullptr) return nullptr;
  return ResolvedType(*type, typedefs_);
}

// The declared type of a variable an assignment writes by its name, the block's
// own declarations and the subroutine's formals hiding the module's. A select
// or member of it, and a name with an unpacked dimension, carry no type here.
const DataType* TaggedContextWalk::TypeOfName(const Expr* target) const {
  if (target->kind != ExprKind::kIdentifier) return nullptr;
  for (size_t i = locals_.size(); i > 0; --i) {
    if (locals_[i - 1].first == target->text) return locals_[i - 1].second;
  }
  auto it = module_types_.find(target->text);
  return it == module_types_.end() ? nullptr : it->second;
}

void TaggedContextWalk::ReportNoMember(const Expr* e, const DataType* context) {
  const std::string_view kTag = e->rhs->text;
  if (context->kind == DataTypeKind::kNamed) {
    diag_.Error(e->range.start,
                std::format("tagged union '{}' has no member named '{}'",
                            context->type_name, kTag),
                Subclause("11.9"));
    return;
  }
  diag_.Error(e->range.start,
              std::format("tagged union has no member named '{}'", kTag),
              Subclause("11.9"));
}

// §11.9: the expression after the member name shall have that member's type,
// a void member taking none. A member whose type is a tagged union gives its
// value the context a tagged expression written there is checked against.
void TaggedContextWalk::CheckTaggedValue(const Expr* e,
                                         const StructMember& member) {
  if (e->lhs == nullptr) return;
  if (member.type_kind == DataTypeKind::kVoid) {
    diag_.Error(e->lhs->range.start,
                std::format("void member '{}' of a tagged union takes no value",
                            member.name),
                Subclause("11.9"));
    return;
  }
  if (!member.unpacked_dims.empty()) return;
  DataType written;
  written.kind = member.type_kind;
  written.type_name = member.type_name;
  written.scope_name = member.scope_name;
  const DataType* type = member.nested_type ? member.nested_type : &written;
  CheckTagged(e->lhs, type);
  const DataType* resolved = Resolve(type);
  if (resolved != nullptr && IsUnpackedAggregateType(*resolved) &&
      IsValueLiteral(e->lhs)) {
    diag_.Error(e->lhs->range.start,
                std::format("value of tagged member '{}' is not assignment "
                            "compatible with its type",
                            member.name),
                Subclause("11.9"));
  }
}

// §11.9: a tagged union expression stands where its context gives it a type,
// which shall be a tagged union having the member named after `tagged`. A
// conditional hands its context to both arms (§11.4.11).
void TaggedContextWalk::CheckTagged(const Expr* e, const DataType* context) {
  if (e == nullptr || context == nullptr) return;
  if (e->kind == ExprKind::kTernary) {
    CheckTagged(e->true_expr, context);
    CheckTagged(e->false_expr, context);
    return;
  }
  if (e->kind != ExprKind::kTagged) return;
  const DataType* resolved = Resolve(context);
  if (resolved == nullptr) return;
  if (resolved->kind != DataTypeKind::kUnion || !resolved->is_tagged) {
    diag_.Error(e->range.start,
                "tagged union expression in a context whose type is not a "
                "tagged union",
                Subclause("11.9"));
    return;
  }
  for (const auto& member : resolved->struct_members) {
    if (member.name == e->rhs->text) {
      CheckTaggedValue(e, member);
      return;
    }
  }
  ReportNoMember(e, context);
}

// §6.24.1: a cast to a type the module names gives its operand that type.
void TaggedContextWalk::CheckCast(const Expr* e) {
  const std::string_view kName = e->rhs != nullptr ? e->rhs->text : e->text;
  if (!typedefs_.contains(kName)) return;
  DataType named;
  named.kind = DataTypeKind::kNamed;
  named.type_name = kName;
  CheckTagged(e->lhs, &named);
}

// §13.5: an actual binds to a formal by position or by name, and the formal's
// type is the context of the actual. Only a call naming a function of this
// module by its bare name reaches one of `functions_`; a method's, a
// hierarchical name's and a compilation unit's function are other functions.
void TaggedContextWalk::CheckCallArgs(const Expr* e) {
  if (e->lhs->kind != ExprKind::kIdentifier || !e->lhs->scope_prefix.empty())
    return;
  auto it = functions_.find(e->callee);
  if (it == functions_.end()) return;
  const auto& formals = it->second->func_args;
  const size_t kPositional = e->args.size() - e->arg_names.size();
  for (size_t i = 0; i < formals.size(); ++i) {
    const int kAt = ResolveActualArgIndex(e, i, formals[i].name, kPositional);
    if (kAt >= 0 && formals[i].unpacked_dims.empty())
      CheckTagged(e->args[static_cast<size_t>(kAt)], &formals[i].data_type);
  }
}

void TaggedContextWalk::WalkExpr(const Expr* e) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCast) CheckCast(e);
  if (e->kind == ExprKind::kCall) CheckCallArgs(e);
  WalkExpr(e->lhs);
  WalkExpr(e->rhs);
  WalkExpr(e->condition);
  WalkExpr(e->true_expr);
  WalkExpr(e->false_expr);
  WalkExpr(e->base);
  WalkExpr(e->index);
  WalkExpr(e->index_end);
  for (const auto* arg : e->args) WalkExpr(arg);
  for (const auto* elem : e->elements) WalkExpr(elem);
}

void TaggedContextWalk::CheckAssigned(const Expr* target, const Expr* value) {
  CheckTagged(value, TypeOfName(target));
  WalkExpr(target);
  WalkExpr(value);
}

// §11.9 names no statement a tagged expression's context is suspended in, so
// the walk descends every link ForEachChildStmt names. A declaration a block
// makes is visible to the statements after it in that block and no further.
void TaggedContextWalk::WalkStmt(const Stmt* s) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    locals_.emplace_back(s->var_name, s->var_unpacked_dims.empty()
                                          ? &s->var_decl_type
                                          : nullptr);
    CheckTagged(s->var_init, locals_.back().second);
    WalkExpr(s->var_init);
    return;
  }
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckAssigned(s->lhs, s->rhs);
  } else {
    WalkExpr(s->lhs);
    WalkExpr(s->rhs);
  }
  if (s->kind == StmtKind::kReturn) CheckTagged(s->expr, return_type_);
  WalkExpr(s->expr);
  WalkExpr(s->condition);
  WalkExpr(s->for_cond);
  const size_t kDepth = locals_.size();
  ForEachChildStmt(s, [this](Stmt* const& sub) { WalkStmt(sub); });
  locals_.resize(kDepth);
}

void TaggedContextWalk::Run(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl) {
      module_types_[item->name] =
          item->unpacked_dims.empty() ? &item->data_type : nullptr;
    }
    if (item->kind == ModuleItemKind::kFunctionDecl)
      functions_[item->name] = item;
  }
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl) {
      CheckTagged(item->init_expr, module_types_[item->name]);
      WalkExpr(item->init_expr);
    }
    if (item->kind == ModuleItemKind::kContAssign)
      CheckAssigned(item->assign_lhs, item->assign_rhs);
    if (IsProceduralItemKind(item->kind)) WalkStmt(item->body);
    return_type_ = item->kind == ModuleItemKind::kFunctionDecl
                       ? &item->return_type
                       : nullptr;
    for (const auto& arg : item->func_args) {
      locals_.emplace_back(
          arg.name, arg.unpacked_dims.empty() ? &arg.data_type : nullptr);
    }
    for (const Stmt* s : item->func_body_stmts) WalkStmt(s);
    locals_.clear();
  }
}

}  // namespace

// §11.9 (printed page 304), which §7.3.2 defers the rule to: a tagged union
// expression takes its type from its context -- an assignment's target, a
// declaration's, a cast's type, a function's return type, a formal's -- and
// shall name a member of that type with a value of the member's type.
void ElaboratorOperationRules::ValidateTaggedUnionMembers(
    const ModuleDecl* decl) {
  TaggedContextWalk(typedefs_, diag_).Run(decl);
}

}  // namespace delta
