#pragma once

#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/property_rewrite.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

void ValidateMulticlockSequences(const PropertyExprNode* node,
                                 const std::vector<EventExpr>& leading,
                                 SourceLoc loc,
                                 const PropertyRegistry& registry,
                                 DiagEngine& diag);

void ValidateMulticlockSequence(const ModuleItem* seq,
                                const std::vector<EventExpr>& leading,
                                SourceLoc loc, const PropertyRegistry& registry,
                                DiagEngine& diag);

}  // namespace delta
