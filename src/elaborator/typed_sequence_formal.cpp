#include "elaborator/typed_sequence_formal.h"

#include <algorithm>
#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/elaborator_helpers.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

bool IsSequenceFormalTypeAllowed(SequenceFormalTypeKind kind) {
  switch (kind) {
    case SequenceFormalTypeKind::kUntyped:
    case SequenceFormalTypeKind::kSequence:
    case SequenceFormalTypeKind::kEvent:
    case SequenceFormalTypeKind::kIntegralOrUserType:
      return true;
    case SequenceFormalTypeKind::kForbidden:
      return false;
  }
  return false;
}

bool IsSequenceTypedFormalRefLegal(SequenceTypedFormalRefPlace where) {
  switch (where) {
    case SequenceTypedFormalRefPlace::kSequenceExprPosition:
    case SequenceTypedFormalRefPlace::kTriggeredMethodOperand:
    case SequenceTypedFormalRefPlace::kMatchedMethodOperand:
      return true;
    case SequenceTypedFormalRefPlace::kOtherPosition:
      return false;
  }
  return false;
}

bool IsEventTypedFormalRefLegal(bool in_event_expression_position) {
  return in_event_expression_position;
}

bool IsSequenceTypedFormalAllowedAsGotoOperand() {
  // §16.8.1: a sequence-typed formal may not be the expression_or_dist
  // operand of a goto_repetition. §16.9.2 lays out the same restriction
  // from the goto side (goto/nonconsecutive repetition applies only to
  // Boolean expressions, never to sequence_exprs).
  return false;
}

bool IsTypedFormalAllowedAsMatchItemLvalue(bool is_local_var_formal) {
  // §16.8.1: outside the local-variable carve-out, a typed formal reference
  // cannot stand as the variable_lvalue in an operator_assignment or
  // inc_or_dec_expression that lives inside a sequence_match_item.
  return is_local_var_formal;
}

bool IsDelayOrRepetitionIndexTypeAllowed(SequenceFormalIntegralType t) {
  switch (t) {
    case SequenceFormalIntegralType::kShortint:
    case SequenceFormalIntegralType::kInt:
    case SequenceFormalIntegralType::kLongint:
      return true;
    case SequenceFormalIntegralType::kOtherIntegral:
      return false;
  }
  return false;
}

TypedFormalSubstitutionMode TypedFormalSubstitution(
    bool actual_is_variable_lvalue) {
  // §16.8.1: an actual that is a variable_lvalue keeps its mutation
  // semantics — the formal acts as the lvalue and writes back to the
  // actual. Otherwise the actual is cast to the formal's type before being
  // spliced into the body during rewriting (§F.4.1).
  return actual_is_variable_lvalue
             ? TypedFormalSubstitutionMode::kAssignBackAfterUpdate
             : TypedFormalSubstitutionMode::kCastBeforeSubstitution;
}

bool IsUntypedKeywordRequired(bool prev_formal_in_list_was_typed,
                              bool this_formal_intended_untyped) {
  // §16.8.1: the keyword is mandatory exactly when an intended-untyped
  // formal would otherwise inherit the data type of a preceding typed
  // formal in the list.
  return prev_formal_in_list_was_typed && this_formal_intended_untyped;
}

bool IsEventTypedFormalCompatibleWithEdgeIdentifierUse(
    bool formal_typed_event, bool actual_combined_with_edge_identifier) {
  // §16.8.1: an event-typed formal is incompatible with an actual that will
  // be combined with an edge_identifier; every other combination is fine.
  return !(formal_typed_event && actual_combined_with_edge_identifier);
}

namespace {

// One typed formal argument of the declaration the rules read: its name, the
// keyword of its type (kEof for a packed vector or a user-defined type), and
// whether it is a local variable formal argument.
struct TypedFormal {
  std::string_view name;
  TokenKind type_kw;
  bool local;
};

// The declaration, its typed formals, and the sink the breaches go to.
struct TypedFormalScope {
  const ModuleItem* decl;
  std::vector<TypedFormal> typed;
  DiagEngine& diag;
};

std::vector<TypedFormal> TypedFormalsOf(const ModuleItem* decl) {
  std::vector<TypedFormal> typed;
  const size_t kCount =
      std::min({decl->prop_formals.size(), decl->prop_formal_type_kw.size(),
                decl->prop_formal_is_local.size()});
  for (size_t i = 0; i < kCount; ++i) {
    if (decl->prop_formal_type_kw[i] == TokenKind::kKwUntyped) continue;
    typed.push_back({decl->prop_formals[i], decl->prop_formal_type_kw[i],
                     decl->prop_formal_is_local[i]});
  }
  return typed;
}

// The integral type a typed formal's keyword gives it as a bound.
SequenceFormalIntegralType BoundTypeOf(TokenKind type_kw) {
  switch (type_kw) {
    case TokenKind::kKwShortint:
      return SequenceFormalIntegralType::kShortint;
    case TokenKind::kKwInt:
      return SequenceFormalIntegralType::kInt;
    case TokenKind::kKwLongint:
      return SequenceFormalIntegralType::kLongint;
    default:
      return SequenceFormalIntegralType::kOtherIntegral;
  }
}

// "formal argument 'f' of 'decl'", as each report names the formal.
std::string FormalOf(const TypedFormalScope& in, const TypedFormal& formal) {
  return "formal argument '" + std::string(formal.name) + "' of '" +
         std::string(in.decl->name) + "'";
}

// The match items written with an operand standing at `loc`.
void CheckMatchItemTargets(const std::vector<SeqMatchAssign>& items,
                           SourceLoc loc, const TypedFormalScope& in) {
  for (const SeqMatchAssign& item : items) {
    for (const TypedFormal& formal : in.typed) {
      if (item.lvar != formal.name ||
          IsTypedFormalAllowedAsMatchItemLvalue(formal.local)) {
        continue;
      }
      in.diag.Error(loc,
                    "the typed " + FormalOf(in, formal) +
                        " is assigned in a sequence match item, which a "
                        "local variable formal argument alone may be",
                    Subclause("16.8.1"));
    }
  }
}

// One bound of a cycle delay range or a repetition, null where none is
// written.
void CheckBound(const Expr* bound, const TypedFormalScope& in) {
  if (bound == nullptr) return;
  for (const TypedFormal& formal : in.typed) {
    const std::unordered_set<std::string_view> kNames = {formal.name};
    if (IsDelayOrRepetitionIndexTypeAllowed(BoundTypeOf(formal.type_kw)) ||
        !ExprMentionsAny(bound, kNames)) {
      continue;
    }
    in.diag.Error(bound->range.start,
                  "the " + FormalOf(in, formal) +
                      " bounds a cycle delay or a repetition but is of a "
                      "type other than shortint, int or longint",
                  Subclause("16.8.1"));
  }
}

// The bounds of a cycle delay range or a repetition. A count written alone,
// `##d` or `[*n]`, is held as the one expression standing as both bounds.
void CheckBounds(const SeqCycleDelay& range, const TypedFormalScope& in) {
  CheckBound(range.min_expr, in);
  if (range.max_expr != range.min_expr) CheckBound(range.max_expr, in);
}

// The operand `operand` of a goto repetition.
void CheckGotoOperand(const Expr* operand, const TypedFormalScope& in) {
  for (const TypedFormal& formal : in.typed) {
    if (formal.type_kw != TokenKind::kKwSequence ||
        !IsNameRef(operand, formal.name)) {
      continue;
    }
    in.diag.Error(operand->range.start,
                  "the " + FormalOf(in, formal) +
                      " is of type sequence and is the operand of a goto "
                      "repetition",
                  Subclause("16.8.1"));
  }
}

void CheckTypedFormalsInTree(const PropertyExprNode* tree,
                             const TypedFormalScope& in);

// One chain of a sequence, the chains nested in it aside, and each group
// standing as one of its operands, which holds a sequence of its own.
void CheckTypedFormalsInChain(const SeqLinearBody& chain,
                              const TypedFormalScope& in) {
  for (size_t i = 0; i < chain.operands.size(); ++i) {
    const Expr* operand = chain.operands[i];
    CheckMatchItemTargets(chain.match_items[i], operand->range.start, in);
    CheckTypedFormalsInTree(operand->property_actual, in);
  }
  CheckMatchItemTargets(chain.first_match_items, in.decl->loc, in);
  for (const SeqCycleDelay& delay : chain.delays) CheckBounds(delay, in);
  for (size_t i = 0; i < chain.repetitions.size(); ++i) {
    CheckBounds(chain.repetitions[i], in);
    if (chain.repetitions[i].kind == SeqRepetition::Kind::kGoto) {
      CheckGotoOperand(chain.operands[i], in);
    }
  }
}

void CheckTypedFormalsIn(const SeqLinearBody& body,
                         const TypedFormalScope& in) {
  ForEachBody(body, [&in](const SeqLinearBody& chain) {
    CheckTypedFormalsInChain(chain, in);
  });
}

// The sequences of the property tree under `tree`, null for none.
void CheckTypedFormalsInTree(const PropertyExprNode* tree,
                             const TypedFormalScope& in) {
  ForEachTreeNode(tree, [&in](const PropertyExprNode& node) {
    if (node.sequence != nullptr) {
      CheckTypedFormalsIn(node.sequence->seq_linear, in);
    }
  });
}

}  // namespace

void CheckTypedFormalReferences(const ModuleItem* decl, DiagEngine& diag) {
  const TypedFormalScope kScope{decl, TypedFormalsOf(decl), diag};
  if (kScope.typed.empty()) return;
  CheckTypedFormalsIn(decl->seq_linear, kScope);
  CheckTypedFormalsInTree(decl->prop_body_tree, kScope);
}

}  // namespace delta
