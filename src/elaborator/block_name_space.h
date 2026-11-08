#pragma once

#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"

namespace delta {

class DiagEngine;
struct ModuleItem;
struct Stmt;

using BlockLabel = std::pair<std::string_view, SourceLoc>;

void CollectNameSpaceLabels(const Stmt* s, std::vector<BlockLabel>& out);

void CollectAssertionNameSpaceLabels(const std::vector<ModuleItem*>& items,
                                     std::vector<BlockLabel>& out);

void CheckBlockNameSpace(const std::vector<Stmt*>& stmts,
                         std::unordered_set<std::string_view> names,
                         DiagEngine& diag);

void CheckNestedBlockNameSpaces(const Stmt* s, DiagEngine& diag);

}  // namespace delta
