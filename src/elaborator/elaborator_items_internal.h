#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

struct RtlirModule;
struct ClassDecl;

// §6.20.1: folds and checks the parameter defaults of a class declared inside a
// module, which RegisterClassParams (elaborator_resolve.cpp) does for a class
// declared at compilation-unit scope. `module_scope` is the enclosing module's
// parameter scope, which a default may name; the folded values are recorded
// under their "Class.name" keys in `cu_param_scope`.
// §16.13.4: a bare name of a named sequence in a property's body, which the
// parser read as a boolean, is made the sequence operand it is, in every
// property declaration of `decl`, once the registry names the sequences;
// defined in elaborator_items_assertions.cpp.
void PromoteSequenceInstancesInProperties(const ModuleDecl* decl,
                                          const PropertyRegistry& registry,
                                          Arena& arena);

void RegisterModuleClassParams(const ClassDecl* cls,
                               const ScopeMap& module_scope,
                               ScopeMap& cu_param_scope, Arena& arena,
                               DiagEngine& diag);

// State threaded into RegisterImportedEnumLiterals: the compilation unit (to
// find imported packages), the arena and enum-member name set used to emit
// backing variables, and the typedef map used to size each enum.
struct ImportedEnumCtx {
  const CompilationUnit* unit;
  Arena& arena;
  TypedefMap& typedefs;
  std::unordered_set<std::string_view>& enum_member_names;
};

// §6.19/§26.6: a wildcard package import makes the package's enumeration
// literals visible by their unqualified names. Emit a backing variable per such
// literal into `mod` (the same representation used for a locally declared enum)
// so a bare reference like `COLOR_GREEN` resolves to its value. Covers both
// header and body wildcard imports. A literal an explicit import of `decl`
// names, `import q::FALSE`, is left to that import, which §26.5 gives
// precedence over the wildcard's. Defined in elaborator_typedef.cpp.
void RegisterImportedEnumLiterals(const ModuleDecl* decl, RtlirModule* mod,
                                  const ImportedEnumCtx& ctx);

// §3.12.1 and §6.19: an enumeration declared by a typedef at compilation-unit
// scope declares its literals for every module of the unit, so each is
// emitted into `mod` as an imported package's are, a module's own typedef of
// the same name taking its place when it is elaborated and an explicit import
// of `decl` shadowing a literal it names (§23.9). Defined in
// elaborator_typedef.cpp.
void RegisterCuEnumLiterals(const ModuleDecl* decl, RtlirModule* mod,
                            const ImportedEnumCtx& ctx);

// Maps a net data-type kind to its RTLIR net type, defaulting to kWire for any
// kind that is not a net type. Defined once in elaborator_decls.cpp and shared
// by the translation units that lower net declarations and validate operations.
NetType DataTypeToNetType(DataTypeKind kind);

// §13.3: a formal takes any data_type, an inline structure or union among
// them, and §7.2.1 lays one out member by member, a member naming a typedef of
// an aggregate included. Resolves each formal's inline aggregate members of
// `item`, a function or task declaration, in place against `typedefs`, the
// table of the scope the declaration stands in. Defined in
// elaborator_items_formals.cpp with the two below; elaborator_items.cpp calls
// it for a module's or an interface's own subroutine as
// Elaborator::ElaborateBehavioralItem reaches it.
void ResolveFormalAggregateTypes(ModuleItem* item, const TypedefMap& typedefs,
                                 Arena& arena);

// §8.6 and §13.3: a class method's formal takes any data_type as a module
// subroutine's does, and the typedefs a method's declaration sees are the
// class's own (§8.23) over those of the scope the class stands in, `outer`.
// Resolves each method's inline aggregate formals of `cls`, and of every
// class nested in it, in place. Elaborator::ElaborateModuleClassDecl calls it
// for a class declared in a module or an interface.
void ResolveClassMethodFormalTypes(ClassDecl* cls, const TypedefMap& outer,
                                   Arena& arena);

// §6.18: a forward typedef's definition may stand below a class whose method
// formal names it, so the same again for every class of a module, `classes`
// being the module's class_decls, against the module's complete table.
// Elaborator::ElaborateItems calls it after the item loop.
void ResolveModuleClassFormalTypes(const std::vector<ClassDecl*>& classes,
                                   const TypedefMap& typedefs, Arena& arena);

// §6.18 with §13.3 and §23.9: the same again for every function and task
// among `items`, a module's own, whose formal names a typedef the module
// forward-declares above the subroutine and defines below it, and (§27.3,
// §27.5) for every one written in a generate block of the items, however
// deeply the block nests, since the block's items reach the module's typedefs
// directly; a member naming a typedef the block itself declares, which §27.5
// and §23.9 have stand over the enclosing scope's of the same name, is left
// to the block's own pass. Elaborator::ElaborateItems calls it after the item
// loop beside the class pass, with the module's items and its complete table,
// and Elaborator::ElaborateGenerateItems after a block's item walk, with the
// block's items and the table holding the typedefs the block itself declares,
// above its subroutines or defined below them (§6.18).
void ResolveModuleSubroutineFormalTypes(const std::vector<ModuleItem*>& items,
                                        const TypedefMap& typedefs,
                                        Arena& arena);

// §26.2 and §3.12.1: the same for every subroutine and every class's methods
// of the unit's packages and of the compilation-unit scope, each against the
// typedefs its own scope sees; `typedefs` is the unit's table.
// Elaborator::RegisterCuScopeItems calls it once the table holds the
// packages' and the classes' qualified typedef names.
void ResolveUnitScopeFormalTypes(CompilationUnit* unit,
                                 const TypedefMap& typedefs, Arena& arena);

// Shared file-local helper for the elaborator_items translation units: a name
// is "declared" in a module if it matches any variable, net, or port already
// recorded on the module. Defined once in elaborator_items.cpp; used there and
// by the module-instantiation/port-binding and generate translation units.
bool IsNameDeclared(std::string_view name, const RtlirModule* mod);

// §3.12.1 with §6.21: whether the compilation-unit scope declares `name` as a
// variable or a net, one of the items written outside every design element.
// The unit's items are asked for a data declaration rather than every named
// item, so a unit function's or class's name is not one. Defined in
// elaborator_items.cpp for MaybeCreateImplicitNet; ValidateScopeRules in
// elaborator_scope_rules.cpp keeps a file-local twin, which is to fold into
// this one.
bool UnitDeclaresData(const CompilationUnit* unit, std::string_view name);

// §27.5: "a conditional generate construct" is the if generate construct and
// the case generate construct. Defined in elaborator_generate.cpp and shared
// with the generate-block naming translation unit, so that the one sentence
// deciding which constructs the direct-nesting rules reach is written once.
bool IsConditionalGenerateConstruct(ModuleItemKind k);

// §27.5: whether a generate block "consists of only one item that is itself a
// conditional generate construct" and is "not surrounded by begin-end
// keywords", which makes the construct within it directly nested and the block
// no separate scope. Defined in elaborator_generate.cpp and shared with the
// generate-block naming translation unit, which has to skip the same blocks
// when numbering.
bool IsDirectlyNestedBlock(const std::vector<ModuleItem*>& body,
                           bool has_begin_end);

// §8.25.1: the parameterized-class declarations of a compilation unit, indexed
// by class name, for the constant folder to resolve a `C#(args)::name` access
// against. Only a class with parameter ports can be specialized, so only those
// are in the table. Defined in elaborator_items_udp.cpp and shared with the
// generate translation unit, which installs the same table for the items of a
// generate block that Elaborator::ElaborateItems installs for a module's own.
std::unordered_map<std::string_view, const ClassDecl*> BuildParamClassRegistry(
    const CompilationUnit* unit);

// §6.20.5: specify parameters declared inside a specify block are named
// constants of the enclosing module, exactly like specparams in the main module
// body. Registers each ordinary specparam of the given specify-block item as a
// module constant (a variable carrying its value expression, as wide as
// SpecparamWidth below makes it), and notes its name in the specparam and
// constant name sets so it resolves and rejects illegal assignment like a body
// specparam. PATHPULSE$ entries are path-pulse limits rather than named
// constants and are skipped. A specify block cannot appear in a generate scope,
// so the bare name is used. Defined in elaborator_validate_specify.cpp.
void RegisterSpecifyBlockSpecparams(
    const ModuleItem* item, RtlirModule* mod, const TypedefMap& typedefs,
    std::unordered_set<std::string_view>& specparam_names,
    std::unordered_set<std::string_view>& const_names);

// §6.20.5: how wide a specify parameter is. A range specification gives it that
// range; without one it "takes the range of its final value", the width of the
// expression that states the value; and a declaration offering neither is 32
// bits. A.2.1.1 writes one `specparam_declaration` and §6.20.5 admits it
// "inside a specify block or in the module body", so both declaration sites are
// sized here rather than each keeping a rule of its own - the specify-block
// site had none, recording every specparam 32 bits wide whatever its
// declaration said. Defined in elaborator_items.cpp.
uint32_t SpecparamWidth(const DataType& type, const Expr* init,
                        const TypedefMap& typedefs);

// §17.5/§17.7: the rules that govern what a checker body may contain -- no
// nets, no general `always`, no blocking assignment in an always_ff, only
// event-controlled timing in an initial procedure, and no design element other
// than a further checker -- read for each item of a checker's body, and for
// nothing where `parent_is_checker` is false. Defined in
// elaborator_items_checker_rules.cpp and called from the item-classification
// pass in elaborator_items_udp.cpp.
void CheckCheckerBodyItemRules(const ModuleItem* item, const ModuleDecl* decl,
                               bool parent_is_checker, DiagEngine& diag);

}  // namespace delta
