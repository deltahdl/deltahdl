#pragma once

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

enum class PrefixBoundKind : std::uint8_t { kUnknown, kNoClass, kNamed };

struct PrefixBound {
  PrefixBoundKind kind = PrefixBoundKind::kUnknown;
  std::string_view name;
  const DataType* type = nullptr;
};

PrefixBound PrefixBoundOf(const DataType* type);

const ClassDecl* BoundClass(const PrefixBound& bound,
                            const CompilationUnit* unit);

const DataType* BoundActual(const ClassDecl& cls, size_t i,
                            std::string_view name, const DataType& written);

bool ClassDeclaresType(const ClassDecl& cls, std::string_view name);

bool DeclaresBodyTypeParam(const ClassMember& m);

void EmitPrefixRestricted(std::string_view prefix, SourceLoc loc,
                          DiagEngine& diag);

bool IsScopeSelection(const Expr* e);

bool SelectsThroughName(const Expr* e);

bool NamesLocalScope(const Expr* scope);

std::vector<const std::vector<DataType>*> BaseArgumentLists(
    const ClassDecl& cls);

bool QueriesAType(const Expr* e);

}  // namespace delta
