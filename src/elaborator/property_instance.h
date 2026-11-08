#pragma once

#include <vector>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

class DiagEngine;

class PropertyRegistry;
struct RtlirModule;
struct RtlirModuleInst;

bool TakesBooleanSubstitution(const Expr* instance, const ModuleItem* decl);

std::vector<EventExpr> SubstituteClockEvents(
    const std::vector<EventExpr>& clock, const ActualsByFormal& actuals,
    Arena& arena);

std::vector<EventExpr> SequenceInstanceClock(const ModuleItem* seq,
                                             const Expr* instance,
                                             const PropertyRegistry& registry,
                                             Arena& arena);

std::vector<EventExpr> PropertyInstanceClock(const ModuleItem* decl,
                                             const ActualsByFormal& actuals,
                                             const PropertyRegistry& registry,
                                             Arena& arena);

std::vector<EventExpr> ActualLeadingClock(const Expr* actual,
                                          const PropertyRegistry& registry,
                                          Arena& arena);

std::vector<EventExpr> FormalOpeningClock(const PropertyExprNode* tree,
                                          const ActualsByFormal& actuals,
                                          const PropertyRegistry& registry,
                                          Arena& arena);

const ModuleItem* InstantiatedDecl(const Expr* operand, ModuleItemKind kind,
                                   const PropertyRegistry& registry);

ModuleItem* SequenceInstanceBody(Expr* instance, Arena& arena);

const std::vector<EventExpr>& FlowedBodyClock(const ModuleItem* decl,
                                              const PropertyRegistry& registry);

struct InferredAtInstance {
  std::vector<EventExpr> clock;
  Expr* disable = nullptr;
};

void FillInferredDefaults(Expr* instance, const ModuleItem* decl,
                          const InferredAtInstance& inferred, Arena& arena,
                          DiagEngine* diag = nullptr);

void FillInferredCheckerDefaults(RtlirModuleInst& inst,
                                 const InferredAtInstance& inferred,
                                 Arena& arena);

std::vector<EventExpr> DefaultClockingEvent(const RtlirModule* mod);

Expr* QualifiedInstance(Expr* instance, const PropertyRegistry& registry,
                        Arena& arena);

void PromoteSequenceInstances(PropertyExprNode* node,
                              const PropertyRegistry& registry, Arena& arena);

void NameInstanceByKey(ModuleItem* item, Arena& arena);

}  // namespace delta
