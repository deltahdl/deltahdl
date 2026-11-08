#pragma once

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/sequence_degeneracy.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

SequenceMatchClass ClassifySequenceMatches(const ModuleItem* seq,
                                           const PropertyRegistry& registry);

SequenceMatchClass ClassifyBodyMatches(const SeqLinearBody& body,
                                       const PropertyRegistry& registry);

void ValidateSequenceDegeneracy(const PropertyExprNode* node, SourceLoc loc,
                                const PropertyRegistry& registry,
                                DiagEngine& diag);

void ValidateSequenceUsedAsProperty(const ModuleItem* seq, SourceLoc loc,
                                    const PropertyRegistry& registry,
                                    DiagEngine& diag);

}  // namespace delta
