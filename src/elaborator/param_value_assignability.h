#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/net_data_type.h"
#include "parser/ast_type.h"

namespace delta {

struct CompilationUnit;
struct Expr;
struct ModuleItem;
struct RtlirModule;
struct RtlirParamDecl;

enum class ParamValueKind : uint8_t {
  kUnknown,
  kNumber,
  kStringLiteral,
  kString,
  kEnum,
  kNull,
  kPattern,
  kArray,
  kStructure,
  kClass,
};

struct ParamValueShape {
  ParamValueKind kind = ParamValueKind::kUnknown;
  uint64_t identity = 0;
  std::string class_name;
  std::vector<uint64_t> dims;
  DataType element;
};

using ParamShapeLookup =
    std::function<std::optional<ParamValueShape>(std::string_view)>;

std::optional<ParamValueShape> NoNamedShape(std::string_view name);

struct ParamValueScope {
  const TypeShapeTables& tables;
  const ScopeMap& constants;
  const CompilationUnit* unit = nullptr;
  ParamShapeLookup named = NoNamedShape;
  bool crosses_scopes = true;
};

struct ParamValueWriter {
  const Expr* value;
  const RtlirModule* module;
  const ScopeMap& constants;
  std::string_view prefix;
};

void ReportOverrideNotAssignable(const RtlirParamDecl& pd,
                                 const ParamValueScope& target,
                                 const ParamValueWriter& writer,
                                 DiagEngine& diag);

struct ParamDefaultMismatch {
  SourceLoc loc;
  std::vector<std::string_view> untyped_names;
};

struct ParamModuleSite {
  const RtlirModule& module;
  std::string_view prefix;
};

void RecordParamDefaultMismatches(RtlirModule& mod, std::size_t first,
                                  const ParamValueScope& scope, Arena& arena);

void ReportParamDefaultMismatches(const RtlirModule& mod, DiagEngine& diag);

void ReportProcedureParamValueTypes(const ModuleItem& item,
                                    const ParamModuleSite& site,
                                    const ParamValueScope& scope,
                                    DiagEngine& diag);

void ReportUnitParamValueTypes(const ParamValueScope& scope, DiagEngine& diag);

void ReportSpecializationValueTypes(const DataType& type,
                                    const ParamModuleSite& site,
                                    const ParamValueScope& scope,
                                    DiagEngine& diag);

}  // namespace delta
