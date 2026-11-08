#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

namespace delta {

using PortMap = std::unordered_map<std::string_view, const PortDecl*>;
using SignalSet = std::unordered_set<std::string_view>;

SignalSet CollectSpecparams(const ModuleItem* item);

SignalSet CollectSpecparamsInScope(const ModuleDecl* mod,
                                   const ModuleItem* block);

struct SpecifyConstantExpr {
  std::string_view operand;
  Subclause subclause;
};

void CheckDelayExpr(const Expr* e, SourceLoc loc, const SignalSet& specparams,
                    DiagEngine& diag, SpecifyConstantExpr constant_expr);

void ValidateTimingCheckLimitOperands(const ModuleDecl* mod, DiagEngine& diag);

void ValidateTimingCheckFlags(const ModuleDecl* mod, DiagEngine& diag);

void ValidateTimingCheckLimitNonNegative(const ModuleDecl* mod,
                                         DiagEngine& diag, TimingCheckKind kind,
                                         std::string_view task,
                                         Subclause subclause);
void ValidateConditionExprs(const ModuleDecl* mod, const PortMap& port_map,
                            DiagEngine& diag);
void ValidatePulseControlTerminals(const ModuleDecl* mod,
                                   const PortMap& port_map, DiagEngine& diag);

}  // namespace delta
