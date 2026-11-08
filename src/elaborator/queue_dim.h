#pragma once

#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"

namespace delta {

struct Expr;
struct Stmt;

bool IsQueueDim(const Expr* dim);

uint32_t QueueLevelsFrom(const std::vector<Expr*>& dims, size_t first);

std::optional<int32_t> QueueBoundMaxSize(int64_t bound);

int32_t QueueDimMaxSize(const Expr* dim);

void CheckBlockQueueBounds(const Stmt* s, const ScopeMap& scope,
                           DiagEngine& diag);

}  // namespace delta
