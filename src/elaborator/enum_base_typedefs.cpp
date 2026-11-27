#include "elaborator/enum_base_typedefs.h"

#include <initializer_list>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using TypeNames = std::unordered_map<std::string_view, const DataType*>;

bool IsVectorKind(DataTypeKind kind) {
  return kind == DataTypeKind::kBit || kind == DataTypeKind::kLogic ||
         kind == DataTypeKind::kReg;
}

bool IsAtomKind(DataTypeKind kind) {
  return kind == DataTypeKind::kByte || kind == DataTypeKind::kShortint ||
         kind == DataTypeKind::kInt || kind == DataTypeKind::kLongint ||
         kind == DataTypeKind::kInteger || kind == DataTypeKind::kTime;
}

struct TypeScope {
  TypeNames names;
  std::vector<std::string_view> wildcards;
};

class EnumBaseTypedefs {
 public:
  explicit EnumBaseTypedefs(Arena& arena) : arena_(arena) {}

  void Packages(const CompilationUnit& unit) {
    for (PackageDecl* pkg : unit.packages) {
      scopes_.emplace_back();
      Items(pkg->items);
      packages_[pkg->name] = std::move(scopes_.back().names);
      scopes_.pop_back();
    }
  }

  void Unit(const CompilationUnit& unit) {
    scopes_.emplace_back();
    Items(unit.cu_items);
    for (ClassDecl* cls : unit.classes) Class(*cls);
    for (const std::vector<ModuleDecl*>* decls :
         {&unit.modules, &unit.interfaces, &unit.programs, &unit.checkers}) {
      for (ModuleDecl* decl : *decls) Design(*decl);
    }
    scopes_.pop_back();
  }

 private:
  const DataType* Lookup(std::string_view name) const {
    for (auto scope = scopes_.rbegin(); scope != scopes_.rend(); ++scope) {
      if (auto own = scope->names.find(name); own != scope->names.end())
        return own->second;
      for (std::string_view pkg : scope->wildcards) {
        const DataType* imported = Imported(pkg, name);
        if (imported != nullptr) return imported;
      }
    }
    return nullptr;
  }

  const DataType* Imported(std::string_view pkg, std::string_view name) const {
    auto names = packages_.find(pkg);
    if (names == packages_.end()) return nullptr;
    auto found = names->second.find(name);
    return found == names->second.end() ? nullptr : found->second;
  }

  void Declare(std::string_view name, const DataType& type) {
    if (type.kind == DataTypeKind::kImplicit) return;
    const DataType* declared = &type;
    if (type.kind == DataTypeKind::kNamed && type.scope_name.empty()) {
      if (const DataType* named = Lookup(type.type_name)) {
        DataType stacked = *named;
        StackDims(stacked, type);
        declared = arena_.Create<DataType>(stacked);
      }
    }
    scopes_.back().names[name] = declared;
  }

  static void StackDims(DataType& base, const DataType& use) {
    if (use.packed_dim_left == nullptr || !IsVectorKind(base.kind)) return;
    std::vector<std::pair<Expr*, Expr*>> dims;
    if (base.packed_dim_left != nullptr)
      dims.emplace_back(base.packed_dim_left, base.packed_dim_right);
    dims.insert(dims.end(), base.extra_packed_dims.begin(),
                base.extra_packed_dims.end());
    base.packed_dim_left = use.packed_dim_left;
    base.packed_dim_right = use.packed_dim_right;
    base.extra_packed_dims = std::move(dims);
  }

  void Rebase(DataType& dt) {
    const DataType* named = Lookup(dt.enum_base_name);
    if (named == nullptr) return;
    const bool kVector = IsVectorKind(named->kind);
    const bool kSizedAtom =
        IsAtomKind(named->kind) && dt.packed_dim_left == nullptr;
    if (!kVector && !kSizedAtom) return;
    DataType base = *named;
    StackDims(base, dt);
    dt.enum_base_name_dim_left = dt.packed_dim_left;
    dt.enum_base_name_dim_right = dt.packed_dim_right;
    dt.enum_base_kind = base.kind;
    dt.is_signed = base.is_signed;
    dt.packed_dim_left = base.packed_dim_left;
    dt.packed_dim_right = base.packed_dim_right;
    dt.extra_packed_dims = base.extra_packed_dims;
  }

  void Type(DataType& dt) {
    if (dt.kind == DataTypeKind::kEnum &&
        dt.enum_base_kind == DataTypeKind::kNamed) {
      Rebase(dt);
    }
  }

  void Import(const ImportItem& import) {
    if (import.is_wildcard) {
      scopes_.back().wildcards.push_back(import.package_name);
      return;
    }
    if (const DataType* imported =
            Imported(import.package_name, import.item_name)) {
      scopes_.back().names[import.item_name] = imported;
    }
  }

  void Body(const std::vector<ModuleItem*>& items) {
    scopes_.emplace_back();
    Items(items);
    scopes_.pop_back();
  }

  void GenerateIf(const ModuleItem& item) {
    Body(item.gen_body);
    if (item.gen_else != nullptr) GenerateIf(*item.gen_else);
  }

  void Subroutine(ModuleItem& item) {
    Type(item.return_type);
    for (FunctionArg& arg : item.func_args) Type(arg.data_type);
    scopes_.emplace_back();
    for (Stmt* s : item.func_body_stmts) Statement(s);
    scopes_.pop_back();
  }

  void Item(ModuleItem& item) {
    switch (item.kind) {
      case ModuleItemKind::kTypedef:
        Type(item.typedef_type);
        Declare(item.name, item.typedef_type);
        break;
      case ModuleItemKind::kImportDecl:
        Import(item.import_item);
        break;
      case ModuleItemKind::kGenerateIf:
        GenerateIf(item);
        break;
      case ModuleItemKind::kGenerateFor:
        Body(item.gen_body);
        break;
      case ModuleItemKind::kGenerateCase:
        for (const GenerateCaseItem& choice : item.gen_case_items)
          Body(choice.body);
        break;
      case ModuleItemKind::kFunctionDecl:
      case ModuleItemKind::kTaskDecl:
        Subroutine(item);
        break;
      case ModuleItemKind::kClassDecl:
        if (item.class_decl != nullptr) Class(*item.class_decl);
        break;
      default:
        Type(item.data_type);
        Statement(item.body);
        break;
    }
  }

  void Items(const std::vector<ModuleItem*>& items) {
    for (ModuleItem* item : items) Item(*item);
  }

  void Statement(Stmt* s) {
    if (s == nullptr) return;
    if (s->kind == StmtKind::kBlockItemDecl && s->decl_item != nullptr)
      Item(*s->decl_item);
    if (s->kind == StmtKind::kVarDecl) Type(s->var_decl_type);
    const bool kOpensScope =
        s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork;
    if (kOpensScope) scopes_.emplace_back();
    ForEachChildStmt(s, [this](Stmt* sub) { Statement(sub); });
    if (kOpensScope) scopes_.pop_back();
  }

  void Class(ClassDecl& cls) {
    scopes_.emplace_back();
    for (ClassMember* member : cls.members) {
      if (member->typedef_item != nullptr) Item(*member->typedef_item);
      if (member->kind == ClassMemberKind::kProperty) Type(member->data_type);
      if (member->method != nullptr) Subroutine(*member->method);
      if (member->nested_class != nullptr) Class(*member->nested_class);
    }
    scopes_.pop_back();
  }

  void Design(ModuleDecl& decl) {
    scopes_.emplace_back();
    for (PortDecl& port : decl.ports) Type(port.data_type);
    Items(decl.items);
    scopes_.pop_back();
  }

  Arena& arena_;
  std::vector<TypeScope> scopes_;
  std::unordered_map<std::string_view, TypeNames> packages_;
};

}  // namespace

DataType EnumBaseAsWritten(const DataType& type) {
  DataType base;
  base.kind = type.enum_base_kind;
  base.type_name = type.enum_base_name;
  base.is_signed = type.is_signed;
  base.packed_dim_left = type.packed_dim_left;
  base.packed_dim_right = type.packed_dim_right;
  if (type.enum_base_name.empty() || base.kind == DataTypeKind::kNamed)
    return base;
  base.kind = DataTypeKind::kNamed;
  base.packed_dim_left = type.enum_base_name_dim_left;
  base.packed_dim_right = type.enum_base_name_dim_right;
  return base;
}

void ResolveEnumBaseTypedefs(const std::vector<CompilationUnit*>& units,
                             Arena& arena) {
  EnumBaseTypedefs resolver(arena);
  for (const CompilationUnit* unit : units) resolver.Packages(*unit);
  for (const CompilationUnit* unit : units) resolver.Unit(*unit);
}

}  // namespace delta
