#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"

namespace delta {

PackageDecl* Lowerer::FindPackage(std::string_view name) const {
  if (!design_) return nullptr;
  for (auto* pkg : design_->packages) {
    if (pkg->name == name) return pkg;
  }
  return nullptr;
}

// The key SimContext holds package `pkg`'s class `cls` under for a reference
// through the package scope resolution operator (§26.3), spelled as the source
// spells it. The evaluator builds the same key from `p::C` in
// ResolveClassScope (src/simulator/eval_function.cpp).
static std::string_view QualifiedClassKey(const PackageDecl* pkg,
                                          const ClassDecl* cls, Arena& arena) {
  auto* key = arena.Create<std::string>(std::string(pkg->name) +
                                        "::" + std::string(cls->name));
  return *key;
}

void Lowerer::LowerPackageClass(const PackageDecl* pkg, const ClassDecl* cls) {
  std::string_view key = QualifiedClassKey(pkg, cls, arena_);
  if (ctx_.FindClassType(key)) return;
  LowerClassDecl(cls, pkg->items);
  ctx_.RegisterClassType(key, ctx_.FindClassType(cls->name));
  AliasExportedClassKeys(pkg, cls);
}

void Lowerer::LowerPackageItem(const PackageDecl* pkg, ModuleItem* item) {
  if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
    // §26.5: a declaration of the importing scope, or an earlier import, has
    // already bound the bare name and keeps it.
    if (ctx_.FindClassType(item->class_decl->name)) return;
    ClassTypeInfo* lowered =
        ctx_.FindClassType(QualifiedClassKey(pkg, item->class_decl, arena_));
    if (lowered) {
      ctx_.RegisterClassType(item->class_decl->name, lowered);
    } else {
      LowerPackageClass(pkg, item->class_decl);
    }
  } else if (item->kind == ModuleItemKind::kFunctionDecl ||
             item->kind == ModuleItemKind::kTaskDecl) {
    // §8.24: an out-of-block method body is the class's, not a subroutine of
    // the package; LowerPackageClass attaches it to the class.
    if (!item->method_class.empty()) return;
    if (!ctx_.FindFunction(item->name)) {
      ctx_.RegisterFunction(item->name, item);
    }
  }
}

static bool PackageItemHasName(const ModuleItem* item, std::string_view name) {
  if (item->name == name) return true;
  if (item->kind == ModuleItemKind::kClassDecl && item->class_decl &&
      item->class_decl->name == name)
    return true;
  return false;
}

static bool IsImportOrExportDecl(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kImportDecl ||
         item->kind == ModuleItemKind::kExportDecl;
}

static ModuleItem* FindNamedPackageItem(const PackageDecl* pkg,
                                        std::string_view name) {
  for (auto* item : pkg->items) {
    if (IsImportOrExportDecl(item)) continue;
    if (PackageItemHasName(item, name)) return item;
  }
  return nullptr;
}

// Collects the package names imported by `pkg`, which a wildcard ("*")
// export re-exports from. The caller resolves each name and recurses.
static std::vector<std::string_view> WildcardExportImportNames(
    const PackageDecl* pkg) {
  std::vector<std::string_view> names;
  for (auto* imp_item : pkg->items) {
    if (imp_item->kind != ModuleItemKind::kImportDecl) continue;
    names.push_back(imp_item->import_item.package_name);
  }
  return names;
}

void Lowerer::LowerImportedName(
    PackageDecl* pkg, std::string_view name,
    std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(pkg).second) return;
  if (auto* found = FindNamedPackageItem(pkg, name)) {
    LowerPackageItem(pkg, found);
    // §26.6: an `export pkg::name` makes the given declaration available to a
    // downstream import following the same rules as a direct import. When that
    // declaration is a parameter or variable, its downstream visibility comes
    // from aliasing the unqualified name to the qualified name in the package
    // that declares it. LowerPackageItem only handles subroutines/classes, so
    // alias the data item here from `pkg` -- the origin package where `found`
    // is declared -- so a re-exported constant/variable resolves at runtime.
    AliasPackageDataItem(pkg, found);
    return;
  }
  if (AliasPackageEnumMember(pkg, name)) return;

  auto recurse = [&](std::string_view pkg_name) {
    auto* src = FindPackage(pkg_name);
    if (!src) return;
    auto sub = visited;
    LowerImportedName(src, name, sub);
  };
  auto handle_export = [&](const ImportItem& ex) {
    if (ex.package_name == "*") {
      for (std::string_view src_name : WildcardExportImportNames(pkg))
        recurse(src_name);
    } else if (ex.is_wildcard || ex.item_name == name) {
      recurse(ex.package_name);
    }
  };

  for (auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    handle_export(item->import_item);
  }
}

// State shared by the free helpers that walk one package's export declarations
// for a wildcard import (§26.5). `lower_all`/`lower_named` forward back into
// the owning Lowerer so the recursion lives outside LowerAllImported's own
// body, keeping its cognitive complexity low. Each callback already snapshots
// the visited set, so it is passed by const reference here.
namespace {
struct ReExportWalk {
  PackageDecl* pkg;
  const std::unordered_set<const PackageDecl*>& visited;
  std::function<PackageDecl*(std::string_view)> find_pkg;
  std::function<void(PackageDecl*)> lower_all;
  std::function<void(PackageDecl*, std::string_view)> lower_named;
};

void ReExportAll(const ReExportWalk& w, PackageDecl* src) { w.lower_all(src); }

// Handles `export *::*;`: re-exports everything from each package `pkg`
// imports.
void ReExportWildcardStar(const ReExportWalk& w) {
  for (std::string_view src_name : WildcardExportImportNames(w.pkg)) {
    if (auto* src = w.find_pkg(src_name)) ReExportAll(w, src);
  }
}

// Handles one resolved `export pkg::item;` / `export pkg::*;`.
void ReExportFromPackage(const ReExportWalk& w, PackageDecl* src,
                         const ImportItem& ex) {
  if (ex.is_wildcard) {
    ReExportAll(w, src);
  } else {
    w.lower_named(src, ex.item_name);
  }
}

// Dispatches one export declaration to the matching re-export handler.
void HandleReExport(const ReExportWalk& w, const ImportItem& ex) {
  if (ex.package_name == "*") {
    ReExportWildcardStar(w);
  } else if (auto* src = w.find_pkg(ex.package_name)) {
    ReExportFromPackage(w, src, ex);
  }
}
}  // namespace

void Lowerer::LowerAllImported(
    PackageDecl* pkg, std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(pkg).second) return;
  for (auto* item : pkg->items) {
    if (IsImportOrExportDecl(item)) continue;
    LowerPackageItem(pkg, item);
    // §26.6: mirror the named-import path -- a data declaration reached by
    // lowering all of a (possibly re-exported) package must also be aliased
    // from this package so a wildcard consumer of a re-exported constant or
    // variable can resolve it at runtime.
    AliasPackageDataItem(pkg, item);
  }

  ReExportWalk walk{pkg, visited,
                    [this](std::string_view name) { return FindPackage(name); },
                    [this, &visited](PackageDecl* src) {
                      auto sub = visited;
                      LowerAllImported(src, sub);
                    },
                    [this, &visited](PackageDecl* src, std::string_view name) {
                      auto sub = visited;
                      LowerImportedName(src, name, sub);
                    }};
  for (auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    HandleReExport(walk, item->import_item);
  }
}

// The key the package's own storage for `name` is held under: "pkg.name", the
// one InitPackageDataVariables and RegisterPackageEnumConstants create and
// EvalMemberAccess reads a `pkg::name` by.
static std::string PackageQualifiedName(const PackageDecl* pkg,
                                        std::string_view name) {
  return std::string(pkg->name) + "." + std::string(name);
}

void Lowerer::AliasPackageDataItem(const PackageDecl* pkg,
                                   const ModuleItem* item) {
  // §6.8: a variable is declared with or without an initializer, and
  // InitPackageDataVariables gives both storage; a parameter has one.
  bool is_param = item->kind == ModuleItemKind::kParamDecl;
  bool is_var = item->kind == ModuleItemKind::kVarDecl;
  if (!(is_var || (is_param && item->init_expr))) return;
  AliasImportedPackageName(item->name, PackageQualifiedName(pkg, item->name));
}

// §26.3's own example imports an enumeration literal by name, `import
// q::FALSE`, and §6.19 makes the literal a constant of the package rather than
// an item of it, so FindNamedPackageItem answers nothing for it. The constant
// has storage under "pkg.MEMBER" (RegisterPackageEnumConstants in
// lowerer_register.cpp, every member of every enumeration the package
// declares, the `name[N]` forms of §6.19.2 expanded); a name no item of the
// package carries that has that key is one of those constants, and the bare
// name is bound to it as a parameter's is. Answers whether `name` was one.
bool Lowerer::AliasPackageEnumMember(const PackageDecl* pkg,
                                     std::string_view name) {
  std::string qname = PackageQualifiedName(pkg, name);
  if (ctx_.GetVariables().count(qname) == 0) return false;
  AliasImportedPackageName(name, qname);
  return true;
}

// Whether the module declares `name` itself: as a variable, a port or a net,
// the three LowerModule and LowerChildModules give storage under the instance
// prefix. The wildcard-imported enumeration literals the elaborator emits as
// module variables (RegisterImportedEnumLiterals in
// src/elaborator/elaborator_typedef.cpp) are among the variables.
bool ModuleDeclaresName(const RtlirModule* mod, std::string_view name) {
  if (mod == nullptr) return false;
  for (const auto& var : mod->variables) {
    if (var.name == name) return true;
  }
  for (const auto& port : mod->ports) {
    if (port.name == name) return true;
  }
  for (const auto& net : mod->nets) {
    if (net.name == name) return true;
  }
  return false;
}

// §7.4.2 with §7.4.4 (printed page 154): the index suffixes of the elements
// of the fixed-size array `info` describes, "[1]" for a one-dimensional
// array's second element and "[1][0]" for a two-dimensional array's, each
// dimension's addresses counted from its low bound in declaration order, the
// spelling CreateArrayElements and CreateMultiDimLeaves (lowerer_var.cpp) key
// the element variables by. A one-dimensional array's extent is the lo and
// size pair, a multidimensional array's the per-dimension vectors.
static void CollectElementSuffixes(const ArrayInfo& info, size_t dim,
                                   const std::string& prefix,
                                   std::vector<std::string>& out) {
  bool multi = !info.dim_sizes.empty();
  size_t dims = multi ? info.dim_sizes.size() : 1;
  if (dim == dims) {
    out.push_back(prefix);
    return;
  }
  uint32_t lo = multi ? info.dim_los[dim] : info.lo;
  uint32_t size = multi ? info.dim_sizes[dim] : info.size;
  for (uint32_t i = 0; i < size; ++i) {
    CollectElementSuffixes(info, dim + 1,
                           prefix + "[" + std::to_string(lo + i) + "]", out);
  }
}

// §26.3 (printed page 810) with §7.4.2 (printed 154) and §7.5 (printed
// 157-158): the fixed-size or dynamic array a package `int a[2]` or `int d[]`
// declares, given to the alias `key`: the ArrayInfo CreatePackageArray or
// CreatePackageDynArray (lowerer_package_data.cpp) registered under `qname`,
// which foreach, $size and every element select read the shape from, copied
// under the alias as the queue and the associative array are, and each
// element variable of a fixed-size array, "p1.a[1]", aliased under the
// alias's own spelling of it, "a[1]" under the instance prefix, the key
// FindVariable answers a module's element by. A dynamic array's elements are
// the QueueObject's, which AliasQueue already shares. The alias carried the
// carrier variable alone, so `a[1] = 7` after `import p1::*` wrote bit 1 of
// the 32-bit carrier and `a[1]` read it back as one bit, `foreach (a[i])` ran
// once per bit, `$size(a)` answered the carrier's width, and `d.size()` and
// `d[2]` after the package's own `p1::d = new[3]` answered 0. The shape is
// copied before the alias is registered: the registration inserts into the
// table the found shape lives in.
static void AliasArray(std::string_view key, std::string_view qname,
                       SimContext& ctx, Arena& arena) {
  const ArrayInfo* found = ctx.FindArrayInfo(qname);
  if (found == nullptr) return;
  ArrayInfo info = *found;
  ctx.RegisterArray(key, info);
  if (info.is_dynamic) return;
  std::vector<std::string> suffixes;
  CollectElementSuffixes(info, 0, "", suffixes);
  for (const std::string& suffix : suffixes) {
    auto* elem_key = arena.Create<std::string>(std::string(key) + suffix);
    ctx.AliasVariable(*elem_key, std::string(qname) + suffix);
  }
}

// The per-name records a package variable is entered in beside its storage,
// keyed "pkg.name" as the storage is, given to the alias `key` from the
// declaring package's `qname`: the class the variable is declared with
// (RegisterPackageClassVariables in lowerer_package_class_vars.cpp), which
// TryClassNewAssign (statement_assign_object.cpp) asks for under the target's
// own key before it constructs, so that `p2::h = new` through the exporter
// and `h = new` after a module's `import p1::h` each found no class, built
// nothing and left the handle null; and the real registration
// ShapePackageVariable (lowerer_register.cpp) makes; and the queue or the
// associative array a package `int q[$]` or `int m[string]` declares
// (CreatePackageAggregate in lowerer_package_data.cpp), which FindQueue and
// FindAssocArray answer by their own keys, so that `q.push_back(4)` after
// `import p1::q` and `p2::q.size()` through an exporter reached no object;
// and the fixed-size or dynamic array's shape and elements (AliasArray). A
// string's kind is a flag of the Variable itself, which the alias already
// shares. Shared with AliasUnitDataItems (lowerer_package_data.cpp), which
// binds the unit's items into a module the same way.
void AliasVariableKinds(std::string_view key, std::string_view qname,
                        SimContext& ctx, Arena& arena) {
  std::string_view cls = ctx.GetVariableClassType(qname);
  if (!cls.empty()) ctx.SetVariableClassType(key, cls);
  if (ctx.IsRealVariable(qname)) ctx.RegisterRealVariable(key);
  ctx.AliasQueue(key, qname);
  ctx.AliasAssocArray(key, qname);
  AliasArray(key, qname, ctx, arena);
  // §15.3 and §15.4: a package's semaphore or mailbox the same way, so `s.get`
  // after `import p1::s` and `p2::s` through an export reach the one bucket.
  ctx.AliasSemaphore(key, qname);
  ctx.AliasMailbox(key, qname);
}

// §26.3 makes the imported name visible under its unqualified spelling in the
// scope that wrote the import, which is the instance being lowered; `qname` is
// the "pkg.name" key the package's own storage holds. The binding is keyed by
// the instance so two instances importing a like-named item from two packages
// each read their own, which §26.3 permits: the only conflict it rules illegal
// is between wildcard imports within one scope. The prefix is empty for a top
// module, where the key is the bare name and SimContext::FindVariable's
// ordinary lookup answers it.
void Lowerer::AliasImportedPackageName(std::string_view name,
                                       std::string_view qname) {
  // §26.3 with §27.5: an import written inside a generate block is the
  // block's own, and its names are bound under the prefix the elaborator gave
  // it (RtlirImport::scope_prefix), one of the keys GenerateBlockKeys
  // (sim_context_name_tables.cpp) spells for a process the block elaborated
  // after the import, which SimContext::FindInGenerateBlock reads a variable
  // by and ScopedObjectKeys lists for an array's shape, a queue and the other
  // objects AliasVariableKinds copies, after the block's own declarations and
  // before the module's. A declaration of the module does not shadow such an
  // import, the block's candidate standing nearer the reference than the
  // enclosing scope's declaration, and its key is never a module
  // declaration's, so the check below is the module-level import's alone.
  bool block_import = !import_scope_prefix_.empty();
  // §26.5: a declaration of the importing scope shadows the import. The
  // module's imports are lowered before its variables, ports and nets exist,
  // so that a declaration initializer can read an imported name (§6.8), and a
  // name the module declares is therefore left unbound here rather than found
  // occupied: the declaration binds it, and the name is never recorded as an
  // imported one, which would let an instance below the module read the
  // module's declaration across §23.9's boundary.
  if (!block_import && ModuleDeclaresName(importing_module_, name)) return;
  std::string key =
      inst_prefix_ + std::string(import_scope_prefix_) + std::string(name);
  // §26.5: a parameter of the importing scope shadows the import too, and an
  // explicit import of a name wins over a wildcard one, which LowerImports
  // orders by applying the explicit imports first. Both are already bound under
  // this key, so an occupied key is left alone. The map is read directly rather
  // than through SimContext::FindVariable, which would also answer from an
  // enclosing scope's binding and let one module's import silence another's.
  if (ctx_.GetVariables().count(key) != 0) return;
  auto* stored = arena_.Create<std::string>(key);
  ctx_.AliasVariable(*stored, qname);
  // §26.3 with §8.7 (printed page 184): `h = new` after `import p1::h`
  // constructs an object of the class p1's h is declared with, which
  // TryClassNewAssign asks for under this key, so the class record rides the
  // alias as it rides an export's (AliasExportedName).
  AliasVariableKinds(*stored, qname, ctx_, arena_);
  // §26.3: the import makes this name visible under its unqualified spelling,
  // and that binding belongs to no module. SimContext::FindVariable is told so
  // because it otherwise stops a bare name at the module boundary §23.9 draws,
  // which would hide an imported item from inside every instance. A block
  // import's key is reached through the process's generate prefixes instead
  // and crosses no boundary.
  if (!block_import) ctx_.RegisterImportedName(*stored);
}

void Lowerer::AliasAllPackageDataItems(const PackageDecl* pkg) {
  for (const auto* item : pkg->items) AliasPackageDataItem(pkg, item);
}

void Lowerer::AliasNamedPackageDataItem(const PackageDecl* pkg,
                                        std::string_view item_name) {
  for (const auto* item : pkg->items) {
    if (item->name == item_name) AliasPackageDataItem(pkg, item);
  }
}

void Lowerer::LowerOneImport(const ImportItem& imp) {
  auto* pkg = FindPackage(imp.package_name);
  if (!pkg) return;
  std::unordered_set<const PackageDecl*> visited;
  if (imp.is_wildcard) {
    LowerAllImported(pkg, visited);
    AliasAllPackageDataItems(pkg);
  } else {
    LowerImportedName(pkg, imp.item_name, visited);
    AliasNamedPackageDataItem(pkg, imp.item_name);
  }
}

// The key a module subroutine's own imports are recorded under, in the place
// of the package a package subroutine is declared in: no package can be named
// so, `$` starting no identifier, and PackageScopedKeys puts the key's own
// "key.name" first, which no storage answers, before the imported packages'.
static std::string_view SubroutineImportScopeKey(const RtlirModule* mod,
                                                 const ModuleItem* func,
                                                 Arena& arena) {
  auto* key = arena.Create<std::string>("$import:" + std::string(mod->name) +
                                        "::" + std::string(func->name));
  return *key;
}

// §26.3 with A.2.8: a package import declaration is a block item declaration,
// so a subroutine body may open with one, and the import makes the package's
// names visible in the body's own scope alone -- `function int calc(); import
// p::*; return K * five(); endfunction` reads p's parameter and calls p's
// function though the module never imported p. The body runs in the frame
// EvalFunctionCall (eval_function.cpp) and ExecInlineTaskCall (stmt_exec.cpp)
// push for the call, which carries Scope::package, the package whose
// declarations and imports SimContext::FindInPackageScope and
// FindFunctionInPackageScope answer a bare name from ahead of the instance's
// own. A module subroutine has no package, so its body imports are recorded
// as the imports of a key of its own (SubroutineImportScopeKey) and the key
// is made the subroutine's package: the two lookups then find "p.K" and
// "p::five" through it and nothing under the key itself. The subroutine is
// one declaration however many instances lower it, so a second instance
// finds it recorded and leaves it.
// The import declarations among a subroutine body's block items, in order.
static std::vector<const ImportItem*> BodyImportItems(const ModuleItem* func) {
  std::vector<const ImportItem*> imports;
  for (const Stmt* stmt : func->func_body_stmts) {
    if (stmt == nullptr || stmt->kind != StmtKind::kBlockItemDecl) continue;
    const ModuleItem* decl = stmt->decl_item;
    if (decl != nullptr && decl->kind == ModuleItemKind::kImportDecl) {
      imports.push_back(&decl->import_item);
    }
  }
  return imports;
}

static void LowerSubroutineBodyImports(const RtlirModule* mod, SimContext& ctx,
                                       Arena& arena) {
  for (const ModuleItem* func : mod->function_decls) {
    if (!func->method_class.empty()) continue;
    if (!ctx.SubroutinePackage(func).empty()) continue;
    std::vector<const ImportItem*> imports = BodyImportItems(func);
    if (imports.empty()) continue;
    std::string_view key = SubroutineImportScopeKey(mod, func, arena);
    for (const ImportItem* imp : imports) {
      ctx.RegisterPackageImport(key, imp->package_name,
                                imp->is_wildcard ? "*" : imp->item_name);
    }
    ctx.RegisterSubroutinePackage(func, key);
  }
}

void Lowerer::LowerImports(const RtlirModule* mod) {
  LowerSubroutineBodyImports(mod, ctx_, arena_);
  importing_module_ = mod;
  auto apply_import = [&](const RtlirImport& imp) {
    ImportItem item;
    item.package_name = imp.package_name;
    item.item_name = imp.item_name;
    item.is_wildcard = imp.is_wildcard;
    // §26.3 with §27.5: an import a generate block wrote binds under the
    // block's own prefix, a module's directly under the instance.
    import_scope_prefix_ = imp.scope_prefix;
    LowerOneImport(item);
    import_scope_prefix_ = {};
  };

  // §26.5: an explicit import of a name takes precedence over a wildcard import
  // of the same name. Because AliasImportedPackageName lets the first binding
  // of a name win, the explicitly imported names must be bound before any
  // wildcard import is applied, regardless of the order the import declarations
  // appear in the source. A module-local declaration shadows both kinds of
  // import, which AliasImportedPackageName honours by leaving a name the
  // module declares unbound: the imports are lowered before the module's
  // variables so that a declaration initializer can read an imported name.
  for (const auto& imp : mod->imports)
    if (!imp.is_wildcard) apply_import(imp);
  for (const auto& imp : mod->imports)
    if (imp.is_wildcard) apply_import(imp);
  importing_module_ = nullptr;
  // §3.12.1: the compilation unit's items the module does not declare, the
  // scope searched after the module's own and its imports', bound under the
  // instance's prefix last so that an import of the name keeps it (§26.5).
  AliasUnitDataItems(design_, mod, inst_prefix_, ctx_, arena_);
}

// §26.6 (printed pages 815-816): an export makes a declaration the package
// imported available through the package, an import of it being an import of
// the original -- `package p2; import p1::x; export p1::x; endpackage` makes
// p1::x and p2::x one declaration, so a reference through the exporting
// package's qualifier, `p2::x`, is p1's x. The storage and the registration
// stand under the declaring package's key alone: "p1.x" from
// InitPackageDataVariables or RegisterPackageEnumConstants and "p1::f" from
// RegisterPackageScopedSubroutines (lowerer_register.cpp), which a `p2::x` or
// `p2::f()` never reached, the read answering 0 and the write landing nowhere.
// Each name a package exports is therefore bound under the exporter's key to
// the original. One such name: the package declaring it and its item, null
// for an enumeration literal, which §6.19 makes a constant of the declaring
// package rather than an item of it.
namespace {
struct ExportedName {
  std::string_view name;
  const PackageDecl* origin = nullptr;
  ModuleItem* item = nullptr;
};

using PackageSet = std::unordered_set<const PackageDecl*>;

// §6.19.2 (printed page 121, Table 6-10): a `name[N]` member generates the
// constants name0 through nameN-1 and `name[N:M]` nameN through nameM, the
// written name itself naming none, and RegisterPackageEnumConstants
// (lowerer_register.cpp) creates the storage under the generated names,
// "p1.VAL0" through "p1.VAL2" for `VAL[3]`. The walk held such a member under
// its written name, which no storage answers, so `p2::VAL2` after `import
// p1::*; export p1::*;` was bound to nothing and read 0. Appends to `names`
// the constants the enumeration `type` writes declares, folded as the
// registration folds them (FoldEnumMembers against `values`, the package's
// parameters and the constants before it, which a bound may name), each
// bound in `values` for the members after it.
//
// §6.19 (printed pages 119-120) declares the literals as constants of the
// scope the enumeration is written in, and §7.2 (printed 146) lets a
// structure or union member's type be any data_type, the enum form among
// them, so a literal of a member's inline enumeration is the package's as the
// elaborator's provided-name walk holds it (AddEnumMemberNames in
// elaborator_scope_rules_names.cpp): the members' inline types are descended
// after the type's own literals.
void CollectEnumConstantNames(const DataType& type, ScopeMap& values,
                              Arena& arena,
                              std::vector<std::string_view>& names) {
  for (const RtlirEnumMember& m :
       FoldEnumMembers(type.enum_members, values, arena)) {
    values[m.name] = m.value;
    names.push_back(m.name);
  }
  for (const StructMember& sm : type.struct_members) {
    if (sm.nested_type != nullptr)
      CollectEnumConstantNames(*sm.nested_type, values, arena, names);
  }
}

// The names of the enumeration constants `pkg` declares, on a typedef or on a
// data declaration's own type (Syntax 6-5), each under the name its storage
// is keyed by. The package's parameters are folded into the scope ahead of
// the enumerations after them, as RegisterPackageItemEnumConstants folds
// them, so a bound naming one expands to the same constants.
std::vector<std::string_view> PackageEnumConstantNames(const PackageDecl* pkg,
                                                       Arena& arena) {
  std::vector<std::string_view> names;
  ScopeMap values;
  for (const ModuleItem* item : pkg->items) {
    if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
      if (auto v = ConstEvalInt(item->init_expr, values))
        values[item->name] = *v;
      continue;
    }
    CollectEnumConstantNames(item->typedef_type, values, arena, names);
    CollectEnumConstantNames(item->data_type, values, arena, names);
  }
  return names;
}

// Lists the declarations a package's export declarations hand on, each with
// the package declaring it, a chain of exports followed to the original
// declaration: `export src::name` hands on the one name, `export src::*`
// every name the package imports from src, and `export *::*` every name the
// package imports. A wildcard import contributes every name its source
// provides, the over-approximation the elaborator's walk makes too
// (AddImportedNamesFrom in elaborator_scope_rules_names.cpp), §26.6 handing
// on only what the package's references actually imported. A package already
// on the chain being walked contributes nothing more, which ends a cycle of
// exports.
class ExportedNameWalk {
 public:
  ExportedNameWalk(const RtlirDesign* design, Arena& arena)
      : design_(design), arena_(arena) {}

  void CollectExported(const PackageDecl* pkg, PackageSet visited,
                       std::vector<ExportedName>& out);

 private:
  const PackageDecl* Find(std::string_view name) const;
  const std::vector<std::string_view>& EnumConstantNames(
      const PackageDecl* pkg);
  bool DeclaresEnumConstant(const PackageDecl* pkg, std::string_view name);
  void CollectProvided(const PackageDecl* pkg, PackageSet visited,
                       std::vector<ExportedName>& out);
  void CollectFromExports(const PackageDecl* pkg, const PackageSet& visited,
                          std::vector<ExportedName>& out);
  void CollectImportsFrom(const PackageDecl* pkg, std::string_view src_name,
                          const PackageSet& visited,
                          std::vector<ExportedName>& out);
  void CollectNamed(const PackageDecl* src, std::string_view name,
                    const PackageSet& visited, std::vector<ExportedName>& out);

  const RtlirDesign* design_;
  Arena& arena_;
  // Each package's enumeration constants, expanded once: a package is asked
  // for them by every wildcard import of it the walk follows.
  std::unordered_map<const PackageDecl*, std::vector<std::string_view>>
      enum_names_;
};

const PackageDecl* ExportedNameWalk::Find(std::string_view name) const {
  for (const PackageDecl* pkg : design_->packages) {
    if (pkg->name == name) return pkg;
  }
  return nullptr;
}

const std::vector<std::string_view>& ExportedNameWalk::EnumConstantNames(
    const PackageDecl* pkg) {
  auto it = enum_names_.find(pkg);
  if (it == enum_names_.end()) {
    it = enum_names_.emplace(pkg, PackageEnumConstantNames(pkg, arena_)).first;
  }
  return it->second;
}

bool ExportedNameWalk::DeclaresEnumConstant(const PackageDecl* pkg,
                                            std::string_view name) {
  for (std::string_view m : EnumConstantNames(pkg)) {
    if (m == name) return true;
  }
  return false;
}

// The names `pkg`'s exports hand on.
void ExportedNameWalk::CollectExported(const PackageDecl* pkg,
                                       PackageSet visited,
                                       std::vector<ExportedName>& out) {
  if (!visited.insert(pkg).second) return;
  CollectFromExports(pkg, visited, out);
}

// Every name `pkg` makes visible to a wildcard import of it: its own items,
// its enumeration literals and what its exports hand on.
void ExportedNameWalk::CollectProvided(const PackageDecl* pkg,
                                       PackageSet visited,
                                       std::vector<ExportedName>& out) {
  if (!visited.insert(pkg).second) return;
  for (ModuleItem* item : pkg->items) {
    if (IsImportOrExportDecl(item) || item->name.empty()) continue;
    out.push_back({item->name, pkg, item});
  }
  for (std::string_view m : EnumConstantNames(pkg)) {
    out.push_back({m, pkg, nullptr});
  }
  CollectFromExports(pkg, visited, out);
}

void ExportedNameWalk::CollectFromExports(const PackageDecl* pkg,
                                          const PackageSet& visited,
                                          std::vector<ExportedName>& out) {
  for (const ModuleItem* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    const ImportItem& ex = item->import_item;
    if (ex.package_name == "*" || ex.is_wildcard) {
      CollectImportsFrom(pkg, ex.package_name, visited, out);
    } else if (const PackageDecl* src = Find(ex.package_name)) {
      CollectNamed(src, ex.item_name, visited, out);
    }
  }
}

// What the imports `pkg` writes from the package `src_name` bring in, or
// every import's for the "*" of `export *::*`.
void ExportedNameWalk::CollectImportsFrom(const PackageDecl* pkg,
                                          std::string_view src_name,
                                          const PackageSet& visited,
                                          std::vector<ExportedName>& out) {
  for (const ModuleItem* item : pkg->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& imp = item->import_item;
    if (src_name != "*" && imp.package_name != src_name) continue;
    const PackageDecl* src = Find(imp.package_name);
    if (src == nullptr) continue;
    if (imp.is_wildcard) {
      CollectProvided(src, visited, out);
    } else {
      CollectNamed(src, imp.item_name, visited, out);
    }
  }
}

// The declaration `src::name` reaches: src's own item or enumeration literal
// of that name, or else the one src's exports hand on under it.
void ExportedNameWalk::CollectNamed(const PackageDecl* src,
                                    std::string_view name,
                                    const PackageSet& visited,
                                    std::vector<ExportedName>& out) {
  if (ModuleItem* item = FindNamedPackageItem(src, name)) {
    out.push_back({name, src, item});
    return;
  }
  if (DeclaresEnumConstant(src, name)) {
    out.push_back({name, src, nullptr});
    return;
  }
  std::vector<ExportedName> handed_on;
  CollectExported(src, visited, handed_on);
  for (const ExportedName& e : handed_on) {
    if (e.name == name) out.push_back(e);
  }
}

// Binds one name `pkg` exports under the exporting package's key to the
// declaring package's registration: a subroutine under "pkg::name", the key
// a scoped call resolves by (FindSubroutineTarget in eval_function_hier.cpp),
// and a variable, parameter or enumeration literal under "pkg.name", the key
// EvalMemberAccess reads and ResolveLhsVariable writes a scoped name by. The
// subroutine keeps the declaring package as the scope its body runs in
// (RegisterSubroutinePackage). A class is not yet lowered when this runs and
// is bound under the exporter's "pkg::C" as it is lowered
// (Lowerer::AliasExportedClassKeys); a typedef has a registration of no kind
// and is left, as is a key the package's own declaration holds, §26.3 having
// a declaration of the scope take the name over an import.
void AliasExportedName(const PackageDecl* pkg, const ExportedName& e,
                       SimContext& ctx, Arena& arena) {
  if (e.origin == pkg || e.name.empty()) return;
  bool subroutine =
      e.item != nullptr && (e.item->kind == ModuleItemKind::kFunctionDecl ||
                            e.item->kind == ModuleItemKind::kTaskDecl);
  if (subroutine) {
    if (!e.item->method_class.empty()) return;
    std::string key = std::string(pkg->name) + "::" + std::string(e.name);
    if (ctx.FindFunction(key) != nullptr) return;
    ctx.RegisterFunction(*arena.Create<std::string>(key), e.item);
    return;
  }
  std::string qname = PackageQualifiedName(e.origin, e.name);
  if (ctx.GetVariables().count(qname) == 0) return;
  std::string key = PackageQualifiedName(pkg, e.name);
  if (ctx.GetVariables().count(key) != 0) return;
  std::string_view stored = *arena.Create<std::string>(key);
  ctx.AliasVariable(stored, qname);
  AliasVariableKinds(stored, qname, ctx, arena);
}

}  // namespace

// Every package's exports, bound once the packages' own storage, constants
// and subroutines are registered and ahead of the package initializers and
// of the unit's and the modules' imports (RegisterDesignTypesAndPackages in
// lowerer.cpp), so that a package importing a re-exported name, `import
// p2::x` in p3, finds "p2.x" where SimContext::FindInPackageScope searches
// p3's imports, in a declaration initializer of p3 as in a subroutine body.
void AliasPackageExports(const RtlirDesign* design, SimContext& ctx,
                         Arena& arena) {
  ExportedNameWalk walk(design, arena);
  for (const PackageDecl* pkg : design->packages) {
    std::vector<ExportedName> names;
    walk.CollectExported(pkg, {}, names);
    for (const ExportedName& e : names) AliasExportedName(pkg, e, ctx, arena);
  }
}

// Whether the exports of `exporter` hand on the declaration `name` of `pkg`.
static bool ExportsHandOnName(ExportedNameWalk& walk,
                              const PackageDecl* exporter,
                              const PackageDecl* pkg, std::string_view name) {
  std::vector<ExportedName> names;
  walk.CollectExported(exporter, {}, names);
  for (const ExportedName& e : names) {
    if (e.origin == pkg && e.name == name) return true;
  }
  return false;
}

// §26.6 (printed pages 815-816) with §26.3: a class an export hands on is
// reached through the exporting package's qualifier as through the declaring
// one's -- `p2::C::get()` and `p2::C h` after `import p1::C; export p1::C;`
// name p1's C -- and ResolveClassScope (eval_function.cpp),
// PackageQualifiedClassOf (eval_static_method.cpp) and PackageClassKey
// (lowerer_package_class_vars.cpp) each ask for the class under "pkg::C", the
// key LowerPackageClass binds the declaring package's class by. No class is
// lowered when AliasPackageExports runs, so the exporters' keys are bound here
// as the class is lowered, each to the one ClassTypeInfo the declaring
// package's key holds: the original keeps its declaring package, and a key an
// exporter's own class holds is left, §26.3 having a declaration of the scope
// take the name.
void Lowerer::AliasExportedClassKeys(const PackageDecl* pkg,
                                     const ClassDecl* cls) {
  if (design_ == nullptr) return;
  ClassTypeInfo* info = ctx_.FindClassType(QualifiedClassKey(pkg, cls, arena_));
  if (info == nullptr) return;
  ExportedNameWalk walk(design_, arena_);
  for (const PackageDecl* exporter : design_->packages) {
    bool own =
        exporter == pkg || FindNamedPackageItem(exporter, cls->name) != nullptr;
    if (own || !ExportsHandOnName(walk, exporter, pkg, cls->name)) continue;
    std::string_view key = QualifiedClassKey(exporter, cls, arena_);
    if (ctx_.FindClassType(key) == nullptr) ctx_.RegisterClassType(key, info);
  }
}

void Lowerer::LowerCompilationUnitImports() {
  if (!design_ || !design_->compilation_unit) return;
  const auto& items = design_->compilation_unit->cu_items;
  // §26.5's precedence of an explicit import over a wildcard one holds in the
  // compilation-unit scope as in a module, so the explicit imports bind first.
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (!item->import_item.is_wildcard) LowerOneImport(item->import_item);
  }
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (item->import_item.is_wildcard) LowerOneImport(item->import_item);
  }
}

void Lowerer::LowerUnimportedClassesOf(const PackageDecl* pkg) {
  // LowerClassDecl binds the bare name while it lowers, and a class of the
  // package that extends an earlier one resolves its base through that
  // binding (§8.13), so the bare names are left in place until the whole
  // package is done and only then given back to whatever held them before: a
  // declaration or an import of a scope that this pass must not displace
  // (§26.5). A bare name nothing held stays bound to the package's class.
  std::vector<std::pair<std::string_view, ClassTypeInfo*>> displaced;
  for (const auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kClassDecl || !item->class_decl) continue;
    const ClassDecl* cls = item->class_decl;
    if (ctx_.FindClassType(QualifiedClassKey(pkg, cls, arena_))) continue;
    if (ClassTypeInfo* held = ctx_.FindClassType(cls->name))
      displaced.emplace_back(cls->name, held);
    LowerPackageClass(pkg, cls);
  }
  for (const auto& [name, held] : displaced) ctx_.RegisterClassType(name, held);
}

// The bare names of the packages' classes that no scope has bound when the
// packages' classes are lowered: not a unit class's
// (LowerCompilationUnitClasses binds those first) and not one a unit import
// brought in (LowerCompilationUnitImports), each once.
static std::vector<std::string_view> UnboundPackageClassNames(
    const RtlirDesign* design, SimContext& ctx) {
  std::vector<std::string_view> names;
  for (const auto* pkg : design->packages) {
    for (const auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kClassDecl || !item->class_decl)
        continue;
      std::string_view name = item->class_decl->name;
      bool seen = std::find(names.begin(), names.end(), name) != names.end();
      if (!seen && ctx.FindClassType(name) == nullptr) names.push_back(name);
    }
  }
  return names;
}

// §26.2 (printed page 808) with §6.21 (printed 132-133): a package's
// declaration assignments, its `C h = new;` among them, are made before any
// procedure starts, and a module's variable is initialized at its declaration,
// ahead of the module's own procedures, so a module's `int y = p1::b.get_n();`
// reads the object the package's initializer constructed; the packages'
// classes are therefore lowered here, ahead of every module, for
// ConstructDataClassInitializers (lowerer_package_data.cpp) to construct
// them by. Lowered after the modules, as they were, the construction came
// after the module's initializer, which ran on a null handle. §26.3
// (printed 810): a package's class is visible in a module by import or
// through `p1::C` alone, so a bare name nothing had bound before this pass
// is given back to no class when the pass is done -- bound to the package's
// class, it took the bare name from a module's later import of another
// package's like-named class (LowerPackageItem keeps a bound bare name) --
// and is bound to the class again once the modules are lowered
// (RebindStrayPackageClassNames), the state the pass left behind when it
// ran after them, which a module's `p1::C h; initial h = new` relies on, the
// elaborator naming the class by its bare name (SetVariableTypeInfo in
// src/elaborator/elaborator_decls.cpp). A name a unit class or a unit
// import held keeps its holder, as LowerUnimportedClassesOf gives it back.
void Lowerer::LowerUnimportedPackageClasses() {
  if (!design_) return;
  std::vector<std::string_view> unbound =
      UnboundPackageClassNames(design_, ctx_);
  for (const auto* pkg : design_->packages) LowerUnimportedClassesOf(pkg);
  for (std::string_view name : unbound) {
    stray_package_class_names_.emplace_back(name, ctx_.FindClassType(name));
    ctx_.RegisterClassType(name, nullptr);
  }
}

void Lowerer::RebindStrayPackageClassNames() {
  for (const auto& [name, info] : stray_package_class_names_) {
    if (ctx_.FindClassType(name) == nullptr) ctx_.RegisterClassType(name, info);
  }
}

}  // namespace delta
