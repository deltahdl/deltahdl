#pragma once

#include <functional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

struct DeclaredLocal {
  const DataType* type;
  const std::vector<Expr*>* unpacked;
};
using DeclaredLocals = std::unordered_map<std::string_view, DeclaredLocal>;

struct ReturnCtx {
  const TypedefMap& typedefs;
  const CompilationUnit* unit;
  DeclaredLocals locals;
};

void EnterDeclaredLocals(const std::vector<Stmt*>& items,
                         DeclaredLocals& locals);

void ForEachChildInScope(
    const Stmt* s, const ReturnCtx& ctx,
    const std::function<void(const Stmt*, const ReturnCtx&)>& visit);

struct CheckedType {
  DataType type;
  const ClassDecl* cls = nullptr;
  bool is_string_literal = false;
};

CheckedType CheckedTypeOf(const DataType& declared, const ReturnCtx& ctx);

CheckedType CheckedTypeOfValue(const Expr* e, const ReturnCtx& ctx);

bool ReturnValueFits(const CheckedType& ret, const CheckedType& value,
                     const CompilationUnit* unit);

using ClassMethods = std::unordered_map<const ModuleItem*, const ClassDecl*>;
ClassMethods ClassMethodsOf(const std::vector<ModuleItem*>& items,
                            const CompilationUnit* unit);

DeclaredLocals ClassProperties(const ClassDecl* cls,
                               const CompilationUnit* unit);

DeclaredLocals ScopeVariables(const std::vector<ModuleItem*>& items);

using ClassScopes = std::unordered_map<const ClassDecl*, DeclaredLocals>;
ClassScopes ClassScopesOf(const std::vector<ModuleItem*>& items,
                          const CompilationUnit& unit);

DeclaredLocals SubroutineLocals(const ModuleItem* item,
                                const DeclaredLocals& outer);

class SubroutineScopes {
 public:
  SubroutineScopes(const std::vector<ModuleItem*>& items,
                   const TypedefMap& typedefs, const CompilationUnit& unit);

  bool IsMethod(const ModuleItem* item) const;

  ReturnCtx Around(const ModuleItem* item);

 private:
  ClassMethods methods_;
  ClassScopes classes_;
  const CompilationUnit* unit_;
  ReturnCtx outside_;
};

}  // namespace delta
