#pragma once

#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

uint32_t LocalWidth(TokenKind type_kw);

uint32_t LocalWidth(const SeqLocalDecl& decl, SimContext& ctx, Arena& arena);

bool LocalIs4State(TokenKind type_kw);

bool LocalIsSigned(TokenKind type_kw);

bool LocalIs4State(const SeqLocalDecl& decl, const SimContext& ctx);

bool LocalIsSigned(const SeqLocalDecl& decl, const SimContext& ctx);

SeqLocalDecl LocalFormalDecl(const ModuleItem& decl, size_t index);

DataType LocalDataType(const SeqLocalDecl& decl);

Variable* StandUpLocal(const SeqLocalDecl& decl, const Logic4Vec& value,
                       SimContext& ctx);

Variable* StandUpUnassignedLocal(const SeqLocalDecl& decl, SimContext& ctx,
                                 Arena& arena);

void AssignWholeLocal(Variable& var, const Logic4Vec& value, Arena& arena);

void AssignMatchItem(const SeqMatchAssign& item, Logic4Vec rhs, Variable& local,
                     SimContext& ctx, Arena& arena);

std::vector<Logic4Vec> InitialLocals(const std::vector<SeqLocalDecl>& decls,
                                     SimContext& ctx, Arena& arena);

void ScheduleMatchCall(const Expr* call, SimContext& ctx, Arena& arena);

class AttemptLocalsScope {
 public:
  AttemptLocalsScope(const std::vector<SeqLocalDecl>& decls,
                     std::vector<Logic4Vec>& locals, SimContext& ctx);
  ~AttemptLocalsScope();
  AttemptLocalsScope(const AttemptLocalsScope&) = delete;
  AttemptLocalsScope& operator=(const AttemptLocalsScope&) = delete;

  void Assign(const SeqMatchAssign& item, Arena& arena);

  void AssignItems(const std::vector<SeqMatchAssign>& items, bool init,
                   Arena& arena);

 private:
  std::vector<Logic4Vec>& locals_;
  SimContext& ctx_;
  std::vector<Variable*> vars_;
};

}  // namespace delta
