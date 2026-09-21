#pragma once

#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

namespace delta {

// The scopes a generate construct opens (§27.4) and the hierarchical path
// names that reach into them (§23.6), as the elaborated design carries them
// on each process, continuous assignment, primitive instance, subroutine and
// instance of a generate block: the loop constants and the prefixes in force
// where an item was written, the visibility of a parameter from them (§23.9),
// and a path as a sequence of its steps. Moved out of rtlir.h, which stood
// at the size the assert-no-oversized-source-files job fails at.

// §27.4: the implicit localparam of every enclosing loop generate block -- "an
// integer parameter that has the same name and type as the loop index, and its
// value within each instance of the generate block is the value of the loop
// index at the time the instance was elaborated". Unrolling shares one body AST
// across the instances, so the per-instance values cannot live in the body;
// they ride on whatever the block elaborated to. Outermost enclosing loop
// first. Empty outside any loop generate construct.
using GenBlockConsts = std::vector<std::pair<std::string_view, int64_t>>;

// The name prefixes of the generate block instances enclosing a process or
// continuous assignment, outermost first, with the instance's own prefix last.
// Empty outside any generate construct. A generate block "comprises a separate
// scope and a new level of hierarchy when it is instantiated" (§27.4), and
// declarations in that scope are named under its prefix, while the shared body
// AST still refers to them by their simple names. Carrying the prefixes is what
// lets a reference from inside the block reach the instance's own declaration,
// and §23.9 is why every enclosing one comes too: the search for a name
// "referenced directly (without a hierarchical path) within a ... generate
// block" continues "upward until an item by that name is found or until a
// module, interface, program, or checker boundary is encountered". The
// innermost prefix flattens the whole path into one string, which no reader can
// split back into the steps that search needs.
using GenBlockPrefixes = std::vector<std::string_view>;

// §23.9: whether a parameter declared under `decl_prefix` -- the generate block
// prefix in force where it was written, which RtlirParamDecl::gen_block_prefix
// holds -- is visible to a reference standing in the generate blocks `scopes`.
// §23.9 lists "Generate blocks" among the elements that "define a new scope",
// and rules that an identifier "referenced directly (without a hierarchical
// path)" is declared "locally or within a module, interface, program, checker,
// task, function, named block, or generate block that is higher in the same
// branch of the name tree", so a block's parameter reaches that block and the
// blocks nested inside it and nothing else. A parameter of the module itself
// carries an empty prefix and is visible throughout the module.
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
// `identifier constant_bit_select`. §23.6 forms such a name "by concatenating
// the names of the modules, module instance names, generate blocks, tasks,
// functions, assertion labels, named assertion action blocks, or named blocks
// that contain it", so a generate block instance is a step of one. §27.4
// indexes a loop generate block's instances "by adding the '[genvar value]' to
// the end of the generate block identifier", which is what `index` holds, and
// §23.6 requires the select "if the array name is not the last path element in
// the hierarchical name", so `has_index` distinguishes a loop generate block
// from a conditional one rather than merely recording whether one was written.
//
// A step of an unnamed generate block has an empty `name`. §27.6 gives such a
// block the name genblk<n>, but §23.6 rules that what it declares "can be
// referenced by hierarchical names only from within the block", and no written
// identifier is empty, so the step matches nothing a path outside can spell.
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

}  // namespace delta
