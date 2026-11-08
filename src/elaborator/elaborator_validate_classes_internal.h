#pragma once

#include <cstddef>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/type_eval.h"
#include "elaborator/value_kind.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

struct ClassScope {
  const CompilationUnit* unit = nullptr;
  const std::vector<ModuleItem*>* items = nullptr;
  std::vector<const ClassDecl*> classes;
};

std::vector<ClassScope> DeclaredClassScopes(const CompilationUnit* unit);

const DataType* SpecializationArgument(const std::vector<DataType>& args,
                                       std::size_t index,
                                       std::string_view name);

void ReportSpecializationOverrideMismatches(const DataType& type, SourceLoc loc,
                                            const CompilationUnit* unit,
                                            const TypedefMap& typedefs,
                                            DiagEngine& diag);

inline const ModuleItem* MethodBody(const ModuleItem* method) {
  return method->out_of_block_body != nullptr ? method->out_of_block_body
                                              : method;
}

std::string_view OwnPropertyAssigned(const Stmt* s, const ClassDecl* cls);

bool IsClassDerivedFrom(std::string_view a, std::string_view b,
                        const CompilationUnit* unit);

bool IsClassDeclDerivedFrom(const ClassDecl* a, std::string_view b,
                            const CompilationUnit* unit);

struct SubroutineSite {
  const ModuleItem* sub = nullptr;
  std::vector<const ClassDecl*> inside;
};

std::vector<SubroutineSite> SubroutinesAmong(
    const std::vector<ModuleItem*>& items,
    const std::vector<const ClassDecl*>& classes = {});

bool IsHandleOperand(
    const Expr* e, const std::unordered_set<std::string_view>& names,
    const std::unordered_map<std::string_view, std::string_view>& types,
    const CompilationUnit* unit);

void AddSubroutineHandles(
    const SubroutineSite& site,
    const std::unordered_set<std::string_view>& class_names,
    const CompilationUnit* unit, std::unordered_set<std::string_view>& names,
    std::unordered_map<std::string_view, std::string_view>& types);

bool IsSliceSelect(const Expr* e);
bool IsNonintegralIndex(const Expr* idx, const ValueScope& values);

std::unordered_set<std::string_view> NamesDeclaredUnder(const Stmt* s);
std::unordered_set<std::string_view> CollectMethodLocalNames(
    const ModuleItem* method);

void CheckRandModeVariableNames(
    const Expr* call,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta
