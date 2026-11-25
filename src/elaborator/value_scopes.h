#pragma once

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "parser/ast_type.h"

namespace delta {

struct ClassDecl;
struct ClassMember;
struct CompilationUnit;
struct Expr;
struct ImportItem;
struct ModuleDecl;
struct ModuleItem;
struct Stmt;

struct ValueScope;

struct ScopedValue {
  DataTypeKind kind = DataTypeKind::kImplicit;
  std::size_t dims = 0;
  const std::vector<StructMember>* members = nullptr;
  const ValueScope* where = nullptr;
  const ClassDecl* cls = nullptr;
  const ValueScope* inside = nullptr;
  bool iterator = false;
  std::size_t packed = 0;
  std::string_view std_class = {};
  std::string_view mode = {};
};

enum class SymbolKind : std::uint8_t {
  kOther,
  kData,
  kFunction,
  kType,
  kClass,
  kInstance,
  kValue,
};

struct ValueSymbol {
  SymbolKind kind = SymbolKind::kOther;
  const DataType* type = nullptr;
  std::size_t dims = 0;
  const ValueScope* where = nullptr;
  const ClassDecl* cls = nullptr;
  std::string_view module = {};
  ScopedValue value = {};
  std::string_view mode = {};
};

struct MethodResult {
  bool is_method = false;
  ScopedValue value = {};
};

struct ValueScope {
  const ValueScope* outer = nullptr;
  const ClassDecl* cls = nullptr;
  std::unordered_map<std::string_view, ValueSymbol> names = {};
  std::vector<std::string_view> wildcards = {};
};

class ValueScopes {
 public:
  explicit ValueScopes(const CompilationUnit& unit);

  const ValueScope& Unit() const { return unit_scope_; }

  const ValueScope& PackageScope(std::string_view name) const;

  const ValueScope& ModuleScope(const ModuleDecl& decl) const;

  const ValueScope& ClassScope(const ClassDecl& cls) const;

  const ValueScope* ModuleNamed(std::string_view name) const;

  const ClassDecl* ClassNamed(std::string_view name,
                              const ValueScope& scope) const;

  void DeclareItems(const std::vector<ModuleItem*>& items, ValueScope& scope);

  void DeclareItem(const ModuleItem& item, ValueScope& scope);

  void DeclareStmts(const std::vector<Stmt*>& stmts, ValueScope& scope);

  ScopedValue ValueOf(const Expr& e, const ValueScope& scope) const;

  MethodResult MethodOn(const ScopedValue& receiver, std::string_view name,
                        bool has_with) const;

  void DeclareIterator(const Expr& call, const ValueScope& scope,
                       ValueScope& with) const;

 private:
  void DeclareModule(const ModuleDecl& decl, const ValueScope& outer);

  void DeclareClass(const ClassDecl& cls, ValueScope& scope);

  void DeclareClassMember(const ClassMember& member, ValueScope& scope);

  void DeclareImport(const ImportItem& import, ValueScope& scope) const;

  ValueSymbol Find(std::string_view name, const ValueScope& scope) const;

  const ValueSymbol* FindHere(std::string_view name,
                              const ValueScope& scope) const;

  const ValueSymbol* FindInClass(std::string_view name,
                                 const ClassDecl& cls) const;

  const ClassDecl* BaseOf(const ClassDecl& cls) const;

  const ClassDecl* ClassOfSymbol(const ValueSymbol& symbol) const;

  ValueSymbol FindScoped(std::string_view prefix, std::string_view name,
                         const ValueScope& scope) const;

  ValueSymbol MemberOfClass(const ClassDecl* cls, std::string_view name) const;

  ValueSymbol FindQualified(const DataType& type,
                            const ValueScope& where) const;

  ValueSymbol SymbolNamedBy(const Expr& e, const ValueScope& scope) const;

  ScopedValue Resolve(const DataType& type, std::size_t dims,
                      const ValueScope& where) const;

  ScopedValue ResolveNames(const DataType& type, std::size_t dims,
                           const ValueScope& where) const;

  ScopedValue ResolveName(const DataType& type, const ValueScope& where) const;

  ScopedValue ValueOfSymbol(const ValueSymbol& symbol) const;

  ScopedValue ValueOfIdentifier(const Expr& e, const ValueScope& scope) const;

  ScopedValue ValueOfSelect(const Expr& e, const ValueScope& scope) const;

  ScopedValue ValueOfAccess(const Expr& access, bool has_with,
                            const ValueScope& scope) const;

  ScopedValue ValueOfCast(const Expr& cast, const ValueScope& scope) const;

  ScopedValue ValueOfConcatenation(const Expr& e,
                                   const ValueScope& scope) const;

  ScopedValue ValueOfName(const Expr& name, const Expr& written,
                          const ValueScope& scope) const;

  std::optional<ScopedValue> MemberOf(const ScopedValue& holder,
                                      std::string_view name) const;

  std::optional<ScopedValue> StructMemberOf(const ScopedValue& holder,
                                            std::string_view name) const;

  ValueScope unit_scope_;
  std::unordered_map<std::string_view, ValueScope> packages_;
  std::unordered_map<std::string_view, const ModuleDecl*> module_names_;
  std::unordered_map<const ModuleDecl*, ValueScope> modules_;
  std::unordered_map<const ClassDecl*, ValueScope> classes_;
  mutable int resolving_ = 0;
};

void DeclareFormals(const std::vector<FunctionArg>& formals, ValueScope& scope);

void DeclareResult(const ModuleItem& function, ValueScope& scope);

void DeclareOther(std::string_view name, ValueScope& scope);

void DeclareData(std::string_view name, const DataType& type, std::size_t dims,
                 ValueScope& scope);

bool IsBuiltinMethodNameWithoutArguments(std::string_view name);

}  // namespace delta
