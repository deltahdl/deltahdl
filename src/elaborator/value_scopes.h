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

struct NameScope;

struct ScopedValue {
  DataTypeKind kind = DataTypeKind::kImplicit;
  std::size_t dims = 0;
  const std::vector<StructMember>* members = nullptr;
  const NameScope* where = nullptr;
  const ClassDecl* cls = nullptr;
  const NameScope* inside = nullptr;
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
  kNoData,
};

enum class ConstantKind : std::uint8_t { kNone, kParameter, kSpecparam };

struct ValueSymbol {
  SymbolKind kind = SymbolKind::kOther;
  const DataType* type = nullptr;
  std::size_t dims = 0;
  const NameScope* where = nullptr;
  const ClassDecl* cls = nullptr;
  std::string_view module = {};
  ScopedValue value = {};
  std::string_view mode = {};
  ConstantKind constant = ConstantKind::kNone;
  const Expr* module_specparam = nullptr;
  const ModuleDecl* nested_module = nullptr;
};

struct MethodResult {
  bool is_method = false;
  ScopedValue value = {};
};

struct NameScope {
  const NameScope* outer = nullptr;
  const ClassDecl* cls = nullptr;
  std::unordered_map<std::string_view, ValueSymbol> names = {};
  std::vector<std::string_view> wildcards = {};
};

class ValueScopes {
 public:
  explicit ValueScopes(const CompilationUnit& unit);

  const NameScope& Unit() const { return unit_scope_; }

  const NameScope& PackageScope(std::string_view name) const;

  const NameScope& ModuleScope(const ModuleDecl& decl) const;

  const NameScope& ClassScope(const ClassDecl& cls) const;

  const NameScope* ModuleNamed(std::string_view name) const;

  const ClassDecl* ClassNamed(std::string_view name,
                              const NameScope& scope) const;

  const ClassDecl* ClassDeclaredAs(const DataType& named,
                                   const NameScope& scope) const;

  bool NamesType(const DataType& named, const NameScope& scope) const;

  bool NamesNoType(const DataType& named, const NameScope& scope) const;

  const ModuleDecl* ModuleDeclared(std::string_view name,
                                   const NameScope& scope) const;

  void DeclareItems(const std::vector<ModuleItem*>& items, NameScope& scope);

  void DeclareItem(const ModuleItem& item, NameScope& scope);

  void DeclareStmts(const std::vector<Stmt*>& stmts, NameScope& scope);

  ScopedValue ValueOf(const Expr& e, const NameScope& scope) const;

  ConstantKind ConstantNamedBy(const Expr& name, const NameScope& scope) const;

  ConstantKind ConstantNamed(std::string_view name,
                             const NameScope& scope) const;

  const Expr* ModuleSpecparamValue(std::string_view name,
                                   const NameScope& scope) const;

  bool Declares(std::string_view name, const NameScope& scope) const;

  MethodResult MethodOn(const ScopedValue& receiver, std::string_view name,
                        bool has_with) const;

  void DeclareIterator(const Expr& call, const NameScope& scope,
                       NameScope& with) const;

 private:
  void DeclareModule(const ModuleDecl& decl, const NameScope& outer);

  void DeclareClass(const ClassDecl& cls, NameScope& scope);

  void DeclareClassMember(const ClassMember& member, NameScope& scope);

  void DeclareImport(const ImportItem& import, NameScope& scope) const;

  ValueSymbol Find(std::string_view name, const NameScope& scope) const;

  const ValueSymbol* FindHere(std::string_view name,
                              const NameScope& scope) const;

  const ValueSymbol* FindInClass(std::string_view name,
                                 const ClassDecl& cls) const;

  bool PackageLacks(std::string_view package, std::string_view name) const;

  const ClassDecl* BaseOf(const ClassDecl& cls) const;

  const ClassDecl* ClassOfSymbol(const ValueSymbol& symbol) const;

  ValueSymbol FindScoped(std::string_view prefix, std::string_view name,
                         const NameScope& scope) const;

  ValueSymbol MemberOfClass(const ClassDecl* cls, std::string_view name) const;

  ValueSymbol FindQualified(const DataType& type, const NameScope& where) const;

  ValueSymbol SymbolNamedBy(const Expr& e, const NameScope& scope) const;

  ScopedValue Resolve(const DataType& type, std::size_t dims,
                      const NameScope& where) const;

  ScopedValue ResolveNames(const DataType& type, std::size_t dims,
                           const NameScope& where) const;

  ScopedValue ResolveName(const DataType& type, const NameScope& where) const;

  ScopedValue ValueOfSymbol(const ValueSymbol& symbol) const;

  ScopedValue ValueOfIdentifier(const Expr& e, const NameScope& scope) const;

  ScopedValue ValueOfSelect(const Expr& e, const NameScope& scope) const;

  ScopedValue ValueOfAccess(const Expr& access, bool has_with,
                            const NameScope& scope) const;

  ScopedValue ValueOfCast(const Expr& cast, const NameScope& scope) const;

  ScopedValue ValueOfConcatenation(const Expr& e, const NameScope& scope) const;

  ScopedValue ValueOfName(const Expr& name, const Expr& written,
                          const NameScope& scope) const;

  std::optional<ScopedValue> MemberOf(const ScopedValue& holder,
                                      std::string_view name) const;

  std::optional<ScopedValue> StructMemberOf(const ScopedValue& holder,
                                            std::string_view name) const;

  NameScope unit_scope_;
  std::unordered_map<std::string_view, NameScope> packages_;
  std::unordered_map<std::string_view, const ModuleDecl*> module_names_;
  std::unordered_map<const ModuleDecl*, NameScope> modules_;
  std::unordered_map<const ClassDecl*, NameScope> classes_;
  mutable int resolving_ = 0;
};

void DeclareFormals(const std::vector<FunctionArg>& formals, NameScope& scope);

void DeclareResult(const ModuleItem& function, NameScope& scope);

void DeclareOther(std::string_view name, NameScope& scope);

void DeclareData(std::string_view name, const DataType& type, std::size_t dims,
                 NameScope& scope);

bool IsBuiltinMethodNameWithoutArguments(std::string_view name);

}  // namespace delta
