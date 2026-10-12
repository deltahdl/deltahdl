#include "simulator/pattern_match.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

static const StructFieldInfo* FindMember(const StructTypeInfo& layout,
                                         std::string_view name) {
  for (const auto& field : layout.fields) {
    if (field.name == name) return &field;
  }
  return nullptr;
}

// The member a member access `s.m` or `s.p.m` names of a variable, through
// the layout each prefix has; null where a prefix has none.
static const StructFieldInfo* MemberOfPath(const Expr* e, SimContext& ctx) {
  if (e->rhs == nullptr) return nullptr;
  const StructTypeInfo* base = nullptr;
  if (e->lhs->kind == ExprKind::kIdentifier) {
    base = StructLayoutOfName(e->lhs->text, ctx);
  } else if (e->lhs->kind == ExprKind::kMemberAccess) {
    const StructFieldInfo* outer = MemberOfPath(e->lhs, ctx);
    base = outer != nullptr ? outer->nested : nullptr;
  }
  return base != nullptr ? FindMember(*base, e->rhs->text) : nullptr;
}

// §12.6.1 with §13.4.1: a call's value as a subject, the tag its body returned
// and the layout of its return type.
static PatternSubject CallSubject(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  PatternSubject subject;
  subject.value = EvalWithReturnedTag(expr, ctx, arena, subject.tag);
  if (const ModuleItem* fn = ctx.FindFunction(expr->callee)) {
    subject.layout = ctx.FindStructType(fn->return_type.type_name);
  }
  return subject;
}

// The layout and tag key of what `expr` names in the design's storage: a
// variable, an element of an array, or a member of a structure or union.
static void AddVariableStorage(const Expr* expr, SimContext& ctx, Arena& arena,
                               PatternSubject& subject) {
  if (expr->kind == ExprKind::kIdentifier) {
    subject.layout = StructLayoutOfName(expr->text, ctx);
    subject.tag_key = TagKeyOfName(expr->text, ctx);
  } else if (expr->kind == ExprKind::kSelect) {
    // §7.4 with §12.6: an element of an array of structures or unions has
    // the array's element layout, and its tag stands under ElementTagKey's.
    if (ElementTagKey(expr, ctx, arena, subject.tag_key)) {
      subject.layout = StructLayoutOfName(subject.tag_key, ctx);
    }
  } else if (expr->kind == ExprKind::kMemberAccess) {
    // §7.2 with §12.6: a member of a structure or union has the layout of its
    // own type, and a tagged union member's tag stands under its path.
    subject.field = MemberOfPath(expr, ctx);
    if (subject.field != nullptr) subject.layout = subject.field->nested;
    if (std::string key; TaggedUnionMemberKey(expr, ctx, key)) {
      subject.tag_key = std::move(key);
    }
  }
}

PatternSubject PatternSubjectOf(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->kind == ExprKind::kCall) return CallSubject(expr, ctx, arena);
  PatternSubject subject;
  subject.value = EvalExpr(expr, ctx, arena);
  // §8.5 with §12.6: a class property of a tagged union type is matched against
  // the tag its own object holds, under the property's key.
  std::string name;
  if (expr->kind == ExprKind::kIdentifier) {
    name = std::string(expr->text);
  } else if (expr->kind == ExprKind::kMemberAccess &&
             !expr->is_scope_resolution) {
    BuildLhsName(expr, name);
  }
  std::string key;
  if (const StructTypeInfo* layout =
          name.empty() ? nullptr : PropertyAggregateLayout(name, ctx, key)) {
    subject.layout = layout;
    subject.tag_key = std::move(key);
    return subject;
  }
  AddVariableStorage(expr, ctx, arena, subject);
  return subject;
}

// The member `field` of `subject`: its bits, with its signedness, the layout of
// its own type, and the key a tag of its own stands under, the subject's key
// followed by the member's name as TaggedUnionMemberKey forms it.
static PatternSubject MemberSubject(const PatternSubject& subject,
                                    const StructFieldInfo& field,
                                    Arena& arena) {
  PatternSubject member;
  member.value =
      ExtractBitField(arena, subject.value, field.bit_offset, field.width);
  member.value.is_signed = field.is_signed;
  member.layout = field.nested;
  member.field = &field;
  if (!subject.tag_key.empty())
    member.tag_key = subject.tag_key + "." + std::string(field.name);
  return member;
}

// §12.6: `tagged M p` matches a value whose tag is M and whose member M
// matches p; a void member, which `tagged M` names with no pattern, has
// nothing more to match.
static bool MatchTagged(const Expr* pat, const PatternSubject& subject,
                        const PatternMatchEnv& env) {
  std::string_view tag = pat->rhs->text;
  std::string_view current = subject.tag_key.empty()
                                 ? std::string_view(subject.tag)
                                 : env.ctx.GetVariableTag(subject.tag_key);
  if (!env.types_only && current != tag) return false;
  if (pat->lhs == nullptr) return true;
  const StructFieldInfo* field =
      subject.layout != nullptr ? FindMember(*subject.layout, tag) : nullptr;
  if (field == nullptr) return false;
  return MatchPattern(pat->lhs, MemberSubject(subject, *field, env.arena), env);
}

// §12.6: a structure pattern matches each member its elements name, by
// declaration position, or by the member name a key gives, in any order and
// leaving out any member.
static bool MatchStructure(const Expr* pat, const PatternSubject& subject,
                           const PatternMatchEnv& env) {
  const auto& fields = subject.layout->fields;
  for (size_t i = 0; i < pat->elements.size(); ++i) {
    const Expr* key =
        i < pat->pattern_keys.size() ? pat->pattern_keys[i] : nullptr;
    const StructFieldInfo* field = nullptr;
    if (key != nullptr) {
      field = FindMember(*subject.layout, key->text);
    } else if (i < fields.size()) {
      field = &fields[i];
    }
    if (field == nullptr ||
        !MatchPattern(pat->elements[i],
                      MemberSubject(subject, *field, env.arena), env)) {
      return false;
    }
  }
  return true;
}

bool MatchPattern(const Expr* pat, const PatternSubject& subject,
                  const PatternMatchEnv& env) {
  if (pat->kind == ExprKind::kIdentifier && pat->text == ".*") return true;
  if (pat->kind == ExprKind::kIdentifier && pat->is_pattern_binding) {
    env.bindings.push_back({pat->text, subject.value, subject.layout,
                            subject.tag_key, subject.tag, subject.field});
    return true;
  }
  if (pat->kind == ExprKind::kTagged) return MatchTagged(pat, subject, env);
  if (pat->kind == ExprKind::kAssignmentPattern && subject.layout != nullptr &&
      !subject.layout->is_union) {
    return MatchStructure(pat, subject, env);
  }
  if (env.types_only) return true;
  return env.compare(subject.value, EvalExpr(pat, env.ctx, env.arena),
                     env.case_kind, env.arena);
}

// §12.6: a pattern identifier is a variable of the type of the member it
// binds: a real, a string, a 2-state value or an enumeration as that member
// is (§6.12, §6.16, §6.11.2, §6.19).
static void TypeBoundVariable(std::string_view name,
                              const StructFieldInfo& field, Variable& var,
                              SimContext& ctx) {
  static constexpr DataTypeKind kReal[] = {
      DataTypeKind::kReal, DataTypeKind::kShortreal, DataTypeKind::kRealtime};
  static constexpr DataTypeKind kTwoState[] = {
      DataTypeKind::kBit, DataTypeKind::kByte, DataTypeKind::kShortint,
      DataTypeKind::kInt, DataTypeKind::kLongint};
  var.is_real = std::ranges::find(kReal, field.type_kind) != std::end(kReal);
  var.value.is_real = var.is_real;
  var.is_string = field.type_kind == DataTypeKind::kString;
  var.is_4state =
      std::ranges::find(kTwoState, field.type_kind) == std::end(kTwoState);
  if (ctx.FindEnumType(field.type_name) != nullptr) {
    ctx.SetVariableEnumType(name, field.type_name);
  }
}

void InstallPatternBindings(const std::vector<PatternBinding>& bindings,
                            SimContext& ctx) {
  for (const auto& binding : bindings) {
    Variable* var = ctx.CreateLocalVariable(binding.name, binding.value.width,
                                            binding.value.is_signed);
    var->value = binding.value;
    var->local_layout = binding.layout;
    if (binding.field != nullptr) {
      TypeBoundVariable(binding.name, *binding.field, *var, ctx);
    }
    // §7.3.2: what a tagged union identifier is bound to carries its tag, and
    // that of each member union its active member reaches, which the bound
    // name holds as a variable assigned the value would.
    if (!binding.tag_key.empty()) {
      CopyTagChain(binding.tag_key, std::string(binding.name), binding.layout,
                   ctx, ctx.GetArena());
    } else if (!binding.tag.empty()) {
      ctx.SetVariableTag(binding.name, binding.tag);
    }
  }
}

bool PatternBindsIdentifiers(const Expr* expr) {
  if (expr == nullptr) return false;
  if (expr->kind == ExprKind::kIdentifier) return expr->is_pattern_binding;
  if (PatternBindsIdentifiers(expr->lhs) || PatternBindsIdentifiers(expr->rhs))
    return true;
  return std::any_of(expr->elements.begin(), expr->elements.end(),
                     PatternBindsIdentifiers);
}

// §12.6: a constant expression pattern succeeds when the value equals the
// constant's value, and §12.6.2 matches `e matches p` the same way; the
// narrower operand is extended to the wider's width, as §12.5's case
// comparison is, and every word of the two is compared, not the first alone.
// Both value planes take part: §12.6.1 lets matching ignore bits only in
// casez and casex, so an x or a z bit matches an x or a z bit alone.
bool MatchesClauseValueMatch(const Logic4Vec& value, const Logic4Vec& constant,
                             TokenKind /*case_kind*/, Arena& arena) {
  uint32_t width = std::max(value.width, constant.width);
  bool sign_ext = value.is_signed && constant.is_signed;
  Logic4Vec lhs =
      value.width < width ? ExtendVec(value, width, sign_ext, arena) : value;
  Logic4Vec rhs = constant.width < width
                      ? ExtendVec(constant, width, sign_ext, arena)
                      : constant;
  uint32_t nwords = std::min(lhs.nwords, rhs.nwords);
  for (uint32_t i = 0; i < nwords; ++i) {
    if (lhs.words[i].aval != rhs.words[i].aval ||
        lhs.words[i].bval != rhs.words[i].bval) {
      return false;
    }
  }
  return true;
}

Truth EvalPredicateTruth(const Expr* pred, SimContext& ctx, Arena& arena) {
  if (pred->kind == ExprKind::kBinary && pred->op == TokenKind::kAmpAmpAmp) {
    Truth first = EvalPredicateTruth(pred->lhs, ctx, arena);
    if (first == Truth::kFalse) return first;
    return ClauseConjunction(first, EvalPredicateTruth(pred->rhs, ctx, arena));
  }
  if (pred->kind == ExprKind::kBinary && pred->op == TokenKind::kKwMatches) {
    std::vector<PatternBinding> bindings;
    PatternMatchEnv env{TokenKind::kKwCase, MatchesClauseValueMatch, ctx, arena,
                        bindings};
    if (!MatchPattern(pred->rhs, PatternSubjectOf(pred->lhs, ctx, arena),
                      env)) {
      return Truth::kFalse;
    }
    InstallPatternBindings(bindings, ctx);
    return Truth::kTrue;
  }
  return TruthOf(EvalExpr(pred, ctx, arena));
}

bool EvalMatchesPredicate(const Expr* pred, SimContext& ctx, Arena& arena) {
  return EvalPredicateTruth(pred, ctx, arena) == Truth::kTrue;
}

void BindPatternTypes(const Expr* pred, SimContext& ctx, Arena& arena) {
  if (pred->kind != ExprKind::kBinary) return;
  if (pred->op == TokenKind::kAmpAmpAmp) {
    BindPatternTypes(pred->lhs, ctx, arena);
    BindPatternTypes(pred->rhs, ctx, arena);
  } else if (pred->op == TokenKind::kKwMatches) {
    std::vector<PatternBinding> bindings;
    PatternMatchEnv env{TokenKind::kKwCase,
                        MatchesClauseValueMatch,
                        ctx,
                        arena,
                        bindings,
                        true};
    MatchPattern(pred->rhs, PatternSubjectOf(pred->lhs, ctx, arena), env);
    InstallPatternBindings(bindings, ctx);
  }
}

bool EnterIfPredicate(const Expr* cond, SimContext& ctx, Arena& arena,
                      bool& scoped) {
  scoped = PatternBindsIdentifiers(cond);
  if (!scoped) return EvalExpr(cond, ctx, arena).IsTruthy();
  ctx.PushScope();
  return EvalMatchesPredicate(cond, ctx, arena);
}

}  // namespace delta
