#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>

namespace delta {

struct Expr;

using ScopeMap = std::unordered_map<std::string_view, int64_t>;

std::optional<int64_t> ConstEvalInt(const Expr* expr);

std::optional<int64_t> ConstEvalInt(const Expr* expr, const ScopeMap& scope);

std::optional<double> ConstEvalReal(const Expr* expr);
std::optional<double> ConstEvalReal(const Expr* expr, const ScopeMap& scope);

bool IsConstantExpr(const Expr* expr, const ScopeMap& scope = {});

std::string LongestStaticPrefix(const Expr* expr, const ScopeMap& scope = {});

}
