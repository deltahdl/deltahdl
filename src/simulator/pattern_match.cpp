#include "simulator/pattern_match.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

PatternSubject PatternSubjectOf(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  PatternSubject subject;
  subject.value = EvalExpr(expr, ctx, arena);
  if (expr->kind == ExprKind::kIdentifier) {
    subject.layout = StructLayoutOfName(expr->text, ctx);
    subject.tag_key = TagKeyOfName(expr->text, ctx);
  } else if (std::string key; TaggedUnionMemberKey(expr, ctx, key)) {
    subject.tag_key = std::move(key);
  }
  return subject;
}

static const StructFieldInfo* FindMember(const StructTypeInfo& layout,
                                         std::string_view name) {
  for (const auto& field : layout.fields) {
    if (field.name == name) return &field;
  }
  return nullptr;
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
  if (subject.tag_key.empty() ||
      env.ctx.GetVariableTag(subject.tag_key) != tag) {
    return false;
  }
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
    env.bindings.push_back({pat->text, subject.value});
    return true;
  }
  if (pat->kind == ExprKind::kTagged) return MatchTagged(pat, subject, env);
  if (pat->kind == ExprKind::kAssignmentPattern && subject.layout != nullptr &&
      !subject.layout->is_union) {
    return MatchStructure(pat, subject, env);
  }
  return env.compare(subject.value, EvalExpr(pat, env.ctx, env.arena),
                     env.case_kind, env.arena);
}

void InstallPatternBindings(const std::vector<PatternBinding>& bindings,
                            SimContext& ctx) {
  for (const auto& binding : bindings) {
    Variable* var = ctx.CreateLocalVariable(binding.name, binding.value.width,
                                            binding.value.is_signed);
    var->value = binding.value;
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
// A pattern bit that is x or z is taken as matching either value -- a grant
// §12.6.1 gives only casez and casex -- and a value bit that is x or z reads
// as 0, as ToUint64 reads it.
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
    uint64_t known = lhs.words[i].aval & ~lhs.words[i].bval;
    uint64_t mask = ~rhs.words[i].bval;
    if ((known & mask) != (rhs.words[i].aval & mask)) return false;
  }
  return true;
}

bool EvalMatchesPredicate(const Expr* pred, SimContext& ctx, Arena& arena) {
  if (pred->kind == ExprKind::kBinary && pred->op == TokenKind::kAmpAmpAmp) {
    return EvalMatchesPredicate(pred->lhs, ctx, arena) &&
           EvalMatchesPredicate(pred->rhs, ctx, arena);
  }
  if (pred->kind == ExprKind::kBinary && pred->op == TokenKind::kKwMatches) {
    std::vector<PatternBinding> bindings;
    PatternMatchEnv env{TokenKind::kKwCase, MatchesClauseValueMatch, ctx, arena,
                        bindings};
    if (!MatchPattern(pred->rhs, PatternSubjectOf(pred->lhs, ctx, arena),
                      env)) {
      return false;
    }
    InstallPatternBindings(bindings, ctx);
    return true;
  }
  return EvalExpr(pred, ctx, arena).IsTruthy();
}

}  // namespace delta
