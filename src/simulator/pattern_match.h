#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "lexer/token.h"
#include "simulator/evaluation_internal.h"
#include "simulator/scope.h"

namespace delta {

class Arena;
struct Expr;
struct Stmt;
class SimContext;
struct StructFieldInfo;
struct StructTypeInfo;

struct PatternSubject {
  Logic4Vec value;
  const StructTypeInfo* layout = nullptr;
  std::string tag_key;
  std::string tag;
  const StructFieldInfo* field = nullptr;
};

struct PatternBinding {
  std::string_view name;
  Logic4Vec value;
  const StructTypeInfo* layout = nullptr;
  std::string tag_key;
  std::string tag;
  const StructFieldInfo* field = nullptr;
};

using PatternValueMatch = bool (*)(const Logic4Vec& value,
                                   const Logic4Vec& constant,
                                   TokenKind case_kind, Arena& arena);

PatternSubject PatternSubjectOf(const Expr* expr, SimContext& ctx,
                                Arena& arena);

struct PatternMatchEnv {
  TokenKind case_kind;
  PatternValueMatch compare;
  SimContext& ctx;
  Arena& arena;
  std::vector<PatternBinding>& bindings;
  bool types_only = false;
};

bool MatchPattern(const Expr* pat, const PatternSubject& subject,
                  const PatternMatchEnv& env);

void InstallPatternBindings(const std::vector<PatternBinding>& bindings,
                            SimContext& ctx);

bool PatternBindsIdentifiers(const Expr* expr);

bool MatchesClauseValueMatch(const Logic4Vec& value, const Logic4Vec& constant,
                             TokenKind case_kind, Arena& arena);

bool EvalMatchesPredicate(const Expr* pred, SimContext& ctx, Arena& arena);

Truth EvalPredicateTruth(const Expr* pred, SimContext& ctx, Arena& arena);

void BindPatternTypes(const Expr* pred, SimContext& ctx, Arena& arena);

bool EnterIfPredicate(const Expr* cond, SimContext& ctx, Arena& arena,
                      bool& scoped);

struct UniqueIfChain {
  const Stmt* first_match = nullptr;
  int match_count = 0;
  bool has_final_else = false;
  bool scoped = false;
  Scope bound;
};
UniqueIfChain EvalUniqueIfChain(const Stmt* stmt, SimContext& ctx,
                                Arena& arena);

}  // namespace delta
