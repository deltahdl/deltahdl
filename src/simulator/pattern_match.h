#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "lexer/token.h"
#include "simulator/evaluation_internal.h"

namespace delta {

class Arena;
struct Expr;
class SimContext;
struct StructFieldInfo;
struct StructTypeInfo;

// §12.6 of IEEE 1800-2023: matching a value against a pattern. A pattern is
// an identifier `.id` (always matches, binding id to the value), the wildcard
// `.*` (always matches), a constant expression (matches a value equal to it),
// a tagged union pattern `tagged M p` (matches a value tagged M whose member
// matches p), or a structure pattern `'{p1, ...}` or `'{m1:p1, ...}` (matches
// a structure whose members match the nested patterns). The case statement
// (§12.6.1), the if statement (§12.6.2) and the conditional operator
// (§12.6.3) match through here.

// What a pattern is matched against: the value's bits, the layout of its type
// where it is a structure or a union, and the key its tag is recorded under
// (SimContext::GetVariableTag) where it is a tagged union; no layout and an
// empty key where it is neither, or its storage was not found.
struct PatternSubject {
  Logic4Vec value;
  const StructTypeInfo* layout = nullptr;
  std::string tag_key;
  // The tag of a value no key holds one under, a call's result (§13.4.1),
  // read where `tag_key` is empty.
  std::string tag;
  // The member of a structure or union the value is, whose type a pattern
  // identifier bound to it takes (§12.6); null for any other value.
  const StructFieldInfo* field = nullptr;
};

// A pattern identifier and the value of what it matched, with that value's
// signedness, which the pattern's scope reads the identifier as, and the
// layout of what it matched where that is a structure or union (§12.6 gives
// the identifier the type of the part it matches).
struct PatternBinding {
  std::string_view name;
  Logic4Vec value;
  const StructTypeInfo* layout = nullptr;
  // Where what it matched is a tagged union, the key its tag stands under, or
  // the tag itself where no key holds one, which the identifier takes with the
  // value (§7.3.2); and the member it is, whose type it takes.
  std::string tag_key;
  std::string tag;
  const StructFieldInfo* field = nullptr;
};

// How a constant pattern's value `constant` is compared with the value
// `value` it is matched against. `case_kind` is the case statement's kind,
// TokenKind::kKwCasez or kKwCasex where the comparison ignores z bits, or x
// and z bits (§12.6.1), and TokenKind::kKwCase otherwise.
using PatternValueMatch = bool (*)(const Logic4Vec& value,
                                   const Logic4Vec& constant,
                                   TokenKind case_kind, Arena& arena);

// The subject `expr` gives: its value, and the layout and tag key its storage
// was declared with -- a variable's, a member's of a structure or union, or
// an element's of an array -- or a call's layout and the tag its body
// returned. `expr` is evaluated once.
PatternSubject PatternSubjectOf(const Expr* expr, SimContext& ctx,
                                Arena& arena);

// What a match runs in: how a constant leaf is compared (`compare`, under
// `case_kind`), the simulation it reads, and where the identifiers the
// pattern binds are appended.
struct PatternMatchEnv {
  TokenKind case_kind;
  PatternValueMatch compare;
  SimContext& ctx;
  Arena& arena;
  std::vector<PatternBinding>& bindings;
  // Whether the match only binds each identifier with the type of what it
  // stands for, comparing no tag and no constant (BindPatternTypes).
  bool types_only = false;
};

// Whether `pat` matches `subject`, appending the identifiers it binds to
// `env.bindings`.
bool MatchPattern(const Expr* pat, const PatternSubject& subject,
                  const PatternMatchEnv& env);

// Creates each of `bindings` as a variable of the innermost scope, which the
// caller has pushed.
void InstallPatternBindings(const std::vector<PatternBinding>& bindings,
                            SimContext& ctx);

// Whether `expr` holds a pattern identifier: in a `matches` clause, in a case
// item's pattern, or in a clause of a predicate joined by `&&&`. Such an
// expression needs a scope for the identifiers to live in; any other is
// evaluated as it always was.
bool PatternBindsIdentifiers(const Expr* expr);

// §12.6.2: how a `matches` clause of an if or a conditional predicate compares
// a constant pattern with the value. The two are extended to the wider of
// their widths, by sign where both are signed, and compared bit for bit, x
// and z bits included; `case_kind` is not read.
bool MatchesClauseValueMatch(const Logic4Vec& value, const Logic4Vec& constant,
                             TokenKind case_kind, Arena& arena);

// §12.6.2 and §12.6.3: evaluates the predicate `pred` clause by clause from
// the left, stopping at the first that fails, and answers whether every one
// succeeded. A clause is `e matches p` or an expression, true where it is
// nonzero. The identifiers a `matches` clause binds are created in the
// innermost scope, which the caller has pushed, so the later clauses, and the
// statement or expression the predicate guards, read them.
bool EvalMatchesPredicate(const Expr* pred, SimContext& ctx, Arena& arena);

// §12.6.3: the same predicate as true, false or ambiguous. A `matches` clause
// is true or false; a filter clause is ambiguous where it is x or z
// (ClauseConjunction).
Truth EvalPredicateTruth(const Expr* pred, SimContext& ctx, Arena& arena);

// §12.6.3 with §11.8.1: creates, in the innermost scope, each identifier the
// `matches` clauses of `pred` bind, with the type of the member it stands for
// whether or not the clause matched, so a conditional's second operand can be
// typed where the predicate fails.
void BindPatternTypes(const Expr* pred, SimContext& ctx, Arena& arena);

// §12.6.2: evaluates an if statement's predicate `cond`. One that binds
// pattern identifiers creates them in a scope pushed for it
// (EvalMatchesPredicate), which `scoped` reports, for the caller to pop once
// the true arm has run; any other is true where it is nonzero. Answers whether
// the predicate held. Shared by the unique, unique0 and priority forms of the
// if statement in both executors.
bool EnterIfPredicate(const Expr* cond, SimContext& ctx, Arena& arena,
                      bool& scoped);

}  // namespace delta
