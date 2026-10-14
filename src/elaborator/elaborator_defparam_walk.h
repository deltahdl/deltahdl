#pragma once

// §23.6 with §23.10.1: the walk a defparam's hierarchical name takes down the
// instance hierarchy, one step at a time, and the §23.10.1 judgement of
// whether the parameter it reaches stands outside the hierarchy the statement
// is confined to. Shared by the module parameter and the block parameter
// readings of a defparam (elaborator_defparam.cpp,
// elaborator_defparam_block.cpp).

#include <functional>
#include <vector>

#include "elaborator/elaborator_data.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"

namespace delta {

// Whether the first `prefix.size()` steps of `path` are `prefix`'s.
bool PathStartsWith(const HierPath& path, const HierPath& prefix);

// One instance a path descends into: the module the step left and the
// instance it entered, whose gen_block_path says which generate block
// instances of that module it stands in.
struct PathDescent {
  RtlirModule* from;
  const RtlirModuleInst* inst;
};

// Gives an element of an instance array a module tree of its own
// (ElaboratorData::IsolateArrayElement): the module holding it, the element.
using ElementIsolator = std::function<void(RtlirModule&, RtlirModuleInst&)>;

// Follows every step of `path` but the last down the instance hierarchy from
// `root`, starting inside the generate block instances `writer` names.
//
// A step names a generate block instance or a module instance, and §23.6 makes
// it exactly one of the two: each node of the hierarchical name tree is a scope
// of its own for identifiers, and a module holds its blocks and its instances
// in one scope, so no step can name both. Reading a step as an instance first
// is therefore a decision rather than a guess, and a step that names no
// instance is a block: it is remembered and the instance it qualifies is looked
// for one step further on.
//
// A step carrying an instance select is read as the element of an instance
// array it selects (§23.6 admits one over an instance array as well as over a
// loop generate block). An element deeper than ApplyDefparamsRecursively has
// reached may still share its module with the others, so `isolate`, where
// given, gives the element entered a module tree of its own first, and the
// value a defparam writes there reaches no other element.
//
// Every instance the walk entered is appended to `descents`, for the
// §23.10.1 judgement of where the target stands.
//
// Answers the module the walk ended in with the steps left over after its last
// instance, which name generate block instances or named blocks of it.
struct DefparamPathEnd {
  RtlirModule* mod;
  HierPath blocks;
};

DefparamPathEnd WalkDefparamPath(RtlirModule* root, const HierPath& path,
                                 const HierPath& writer,
                                 std::vector<PathDescent>& descents,
                                 const ElementIsolator& isolate = {});

// The module WalkDefparamPath ends in, or nullptr where steps are left over:
// they name generate block instances nothing was instantiated in, so the path
// reached a scope rather than a module and names none of its parameters.
RtlirModule* DescendDefparamPath(RtlirModule* root, const HierPath& path,
                                 const HierPath& writer,
                                 std::vector<PathDescent>& descents,
                                 const ElementIsolator& isolate = {});

// §23.10.1 (printed page 764): whether the parameter `steps` reaches from the
// top-level module `root` stands outside the generate block instance
// `blocks` records for `writer`, the module whose statement names it -- the
// clause forbids a statement in a hierarchy in or under a generate block
// instance from changing a parameter value outside that hierarchy. Inside it
// is a target the walk reaches by leaving the block's holder into an instance
// standing in that block or in one nested in it; a target the walk reaches
// without passing the holder, the holder's own parameter among them, is
// outside. False for a writer under no block.
bool EscapesWriterBlock(const DefparamWriterBlocks& blocks,
                        const RtlirModule* writer, RtlirModule* root,
                        const HierPath& steps);

}  // namespace delta
