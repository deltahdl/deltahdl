#pragma once

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

namespace delta {

struct EventExpr;
struct ModuleItem;

// The scopes a generate construct opens (§27.4) and the hierarchical path
// names that reach into them (§23.6), as the elaborated design carries them
// on each process, continuous assignment, primitive instance, subroutine and
// instance of a generate block: the loop constants and the prefixes in force
// where an item was written, the visibility of a parameter from them (§23.9),
// and a path as a sequence of its steps. Moved out of rtlir.h, which stood
// at the size the assert-no-oversized-source-files job fails at.

// §27.4: the implicit localparam of every enclosing loop generate block -- an
// integer parameter named and typed as the loop index, holding in each block
// instance the index value at that instance's elaboration. Unrolling shares one
// body AST across the instances, so the per-instance values cannot live in the
// body; they ride on whatever the block elaborated to. Outermost enclosing loop
// first. Empty outside any loop generate construct.
using GenBlockConsts = std::vector<std::pair<std::string_view, int64_t>>;

// The name prefixes of the generate block instances enclosing a process or
// continuous assignment, outermost first, with the instance's own prefix last.
// Empty outside any generate construct. A generate block forms a scope of its
// own and a further level of hierarchy once instantiated (§27.4), and
// declarations in that scope are named under its prefix, while the shared body
// AST still refers to them by their simple names. Carrying the prefixes is what
// lets a reference from inside the block reach the instance's own declaration,
// and §23.9 is why every enclosing one comes too: the search for a name
// referenced without a hierarchical path in a generate block climbs until it
// finds an item of that name or meets a module, interface, program or checker
// boundary. The innermost prefix flattens the whole path into one string, which
// no reader can split back into the steps that search needs.
using GenBlockPrefixes = std::vector<std::string_view>;

// §23.9: whether a parameter declared under `decl_prefix` -- the generate block
// prefix in force where it was written, which RtlirParamDecl::gen_block_prefix
// holds -- is visible to a reference standing in the generate blocks `scopes`.
// §23.9 lists generate blocks among the elements that open a new scope, and
// rules that an identifier referenced without a hierarchical path is declared
// locally or in a module, interface, program, checker, task, function, named
// block or generate block higher in the same branch of the name tree, so a
// block's parameter reaches that block and the blocks nested inside it and
// nothing else. A parameter of the module itself carries an empty prefix and is
// visible throughout the module.
//
// `scopes` holds the prefixes in force at the reference, outermost first. Pass
// an empty list where the reference has no position inside the module to speak
// of -- a reader answering about another module, or one reached through
// RegisteredModule(), which names a module and nothing about where inside it an
// expression stands -- which admits the module's own parameters alone.
inline bool ParamVisibleFromScopes(std::string_view decl_prefix,
                                   const GenBlockPrefixes& scopes) {
  if (decl_prefix.empty()) return true;
  for (std::string_view scope : scopes) {
    if (scope == decl_prefix) return true;
  }
  return false;
}

// §23.6: one step of a hierarchical path name, which Syntax 23-7 writes as
// `identifier constant_bit_select`. §23.6 forms such a name by joining the
// names of the modules, module instances, generate blocks, tasks, functions,
// assertion labels, named assertion action blocks or named blocks that contain
// the item, so a generate block instance is a step of one. §27.4 indexes a loop
// generate block's instances by appending '[genvar value]' to the generate
// block identifier, which is what `index` holds, and §23.6 requires the select
// wherever the array name is not the path's last element, so `has_index`
// distinguishes a loop generate block from a conditional one rather than merely
// recording whether one was written.
//
// A step of an unnamed generate block has an empty `name`. §27.6 gives such a
// block the name genblk<n>, but §23.6 rules that what it declares is reachable
// by hierarchical name only from inside the block, and no written identifier is
// empty, so the step matches nothing a path outside can spell.
struct HierStep {
  std::string_view name;
  bool has_index = false;
  int64_t index = 0;
};

// §23.6: a hierarchical path name as a sequence of its steps. Two things are
// spelled this way. A path a source wrote ends in the object it names, and the
// generate block instances enclosing a declaration are the steps between its
// module and it, outermost first and empty for a declaration of the module
// itself. Comparing the two is what resolves the first, which the flattened
// name a declaration is stored under cannot do: `g_u` is what both `g.u` and a
// module-level instance named `g_u` are spelled as, and §23.6 makes them
// different scopes.
using HierPath = std::vector<HierStep>;

// §27.4 with §13.4 and §23.6: one subroutine declared in a generate block
// instance. The block forms a scope of its own and a further level of
// hierarchy, so the subroutine is a member of the block instance's scope, which
// §23.6 names through the block, `blk[1].triple` for the instance of loop
// generate block blk at index 1, and its body reads the block's own
// declarations and the implicit localparam of each loop it is inside by their
// simple names. Every iteration of a loop generate block elaborates the one
// declaration, so RtlirModule::function_decls holds it once per instance and
// says nothing about which; this entry is what does. `gen_block_path` is the
// path §23.6 names the instance by, and the other two members are what an
// RtlirProcess of the same block carries, for the same reason: the body the
// instances share names the block's declarations plainly, and the process that
// calls the subroutine from outside the block stands in no such scope.
struct RtlirGenBlockSubroutine {
  ModuleItem* decl = nullptr;
  HierPath gen_block_path;
  GenBlockConsts gen_block_consts;
  GenBlockPrefixes gen_block_prefixes;
};

// §27.4 and §27.5 with §23.6: one declaration of a named generate block
// instance, reached from any scope by the path that names the instance and
// then the declaration, `g.v` or `u.g[1].v`. The elaborator stores what the
// block declares under a key that flattens the path into the name, `g_1_v`,
// which a reference inside the block finds through GenBlockPrefixes and a
// hierarchical path cannot spell, so each declaration is listed here with its
// path for the run to register under the key the path spells.
//
// `kStorage` is a variable or net, stored under `storage`. `kParam` is a
// parameter, which RtlirModule::params holds at `param_index` under its simple
// name alone, so no stored key tells one instance's apart from another's.
// `kIndex` is the implicit localparam §27.4 gives a loop block's instance,
// named as the loop index and holding `index_value`, which the run otherwise
// keeps only as a constant of the block's processes. A declaration of an
// unnamed block has no entry: §27.6 leaves such a block no name a hierarchical
// path can use.
struct RtlirGenBlockMember {
  enum class Kind : uint8_t { kStorage, kParam, kIndex };
  Kind kind = Kind::kStorage;
  std::string_view name;
  std::string_view storage;
  size_t param_index = 0;
  int64_t index_value = 0;
  HierPath gen_block_path;
};

// §14.3 with §27.4: a clocking block declared in a generate block instance.
// The run registers the block, so what is kept is what the registration needs
// beyond the item: the prefixes a bare name written in the block resolves
// through (§23.9), which also tell apart the blocks the instances of one loop
// declare, and the path that names the block from outside, `g.cb` (§23.6).
struct RtlirGenBlockClocking {
  // The block's position in RtlirModule::clocking_blocks. The instances of a
  // loop generate block share one body, so the item alone says not which
  // instance declared the entry.
  size_t index = 0;
  const ModuleItem* block = nullptr;
  HierPath gen_block_path;
  GenBlockPrefixes gen_block_prefixes;
};

// §37.12 and §37.51 with §27.4: a property a module body declares, with the
// generate block instance declaring it, which is the scope it belongs to.
struct RtlirPropertyDecl {
  const ModuleItem* item = nullptr;
  // The generate block instances between the module and the declaration,
  // outermost first; empty for a property of the module itself.
  HierPath gen_block_path;
  // §27.4: the prefixes of those instances, innermost last.
  GenBlockPrefixes gen_block_prefixes;
  // §14.3: the clocking block declaring the property, whose scope it belongs
  // to (§37.12); null for a property of the module or the generate block.
  const ModuleItem* clocking_block = nullptr;
};

// §37.49 with §27.4: an assertion a module body writes as an item, with the
// generate block instance it stands in. The instances of a loop generate block
// share one body, so the item alone says not which instance wrote the entry.
struct RtlirAssertion {
  const ModuleItem* item = nullptr;
  // The generate block instances between the module and the assertion,
  // outermost first; empty for an assertion of the module itself.
  HierPath gen_block_path;
  // §27.4: the prefixes of those instances, innermost last, whose
  // declarations a name the assertion writes finds first.
  GenBlockPrefixes gen_block_prefixes;
  // §16.5.2 and §14.14: where the item's leading clock is $global_clock, the
  // event this instance's effective global clocking declaration names; null
  // where the clock written stands.
  const std::vector<EventExpr>* leading_clock = nullptr;
};

// Appends `member` to `members` as a declaration of the generate block instance
// `path`, the steps from the module to it; nothing for a declaration of the
// module itself or of a block with an unnamed step (§27.6).
inline void RecordGenBlockMember(std::vector<RtlirGenBlockMember>& members,
                                 const HierPath& path,
                                 RtlirGenBlockMember member) {
  if (path.empty()) return;
  for (const HierStep& step : path) {
    if (step.name.empty()) return;
  }
  member.gen_block_path = path;
  members.push_back(std::move(member));
}

// §23.3.3.5 with §37.11: the instance array an instance is an element of -
// the array's name as the source wrote it, its declared left and right
// bounds, and the element's own index. An instance outside any array has an
// empty name.
struct InstArrayElement {
  std::string_view name;
  int64_t left = 0;
  int64_t right = 0;
  int64_t index = 0;
};

}  // namespace delta
