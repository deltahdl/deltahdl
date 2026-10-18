#include "elaborator/elaborator_defparam_walk.h"

#include <cstddef>
#include <vector>

#include "elaborator/elaborator_data.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"

namespace delta {

// True when a step of a path a source wrote names the same generate block
// instance a step recorded on a declaration does.
static bool SameHierStep(const HierStep& written, const HierStep& recorded) {
  if (written.name != recorded.name) return false;
  if (written.has_index != recorded.has_index) return false;
  return !written.has_index || written.index == recorded.index;
}

bool PathStartsWith(const HierPath& path, const HierPath& prefix) {
  if (path.size() < prefix.size()) return false;
  for (size_t i = 0; i < prefix.size(); ++i) {
    if (!SameHierStep(prefix[i], path[i])) return false;
  }
  return true;
}

// Whether the instance `child` answers the step `step`: by its name, and for
// a step carrying an instance select by the element of an instance array
// (§23.6) the select names, which RtlirModuleInst::array records. A step holds
// one select, which names an element of a one-dimensional array alone: in an
// array of more dimensions it names no instance.
static bool ChildAnswersStep(const RtlirModuleInst& child,
                             const HierStep& step) {
  if (child.simple_inst_name != step.name) return false;
  if (!step.has_index) return true;
  return child.array.dims.size() == 1 && child.array.index == step.index;
}

// The instance `mod` holds as `step` inside exactly the generate block
// instances `blocks` names, or nullptr when it holds no such thing.
static RtlirModuleInst* ChildUnderBlocks(RtlirModule* mod, const HierStep& step,
                                         const HierPath& blocks) {
  for (auto& child : mod->children) {
    if (!child.resolved) continue;
    if (!ChildAnswersStep(child, step)) continue;
    if (child.gen_block_path.size() != blocks.size()) continue;
    if (PathStartsWith(child.gen_block_path, blocks)) return &child;
  }
  return nullptr;
}

DefparamPathEnd WalkDefparamPath(RtlirModule* root, const HierPath& path,
                                 const HierPath& writer,
                                 std::vector<PathDescent>& descents,
                                 const ElementIsolator& isolate) {
  RtlirModule* cur = root;
  HierPath blocks = writer;
  for (size_t i = 0; i + 1 < path.size(); ++i) {
    RtlirModuleInst* next = ChildUnderBlocks(cur, path[i], blocks);
    if (next != nullptr) {
      if (isolate && path[i].has_index) isolate(*cur, *next);
      descents.push_back({cur, next});
      cur = next->resolved;
      blocks.clear();
      continue;
    }
    blocks.push_back(path[i]);
  }
  return {cur, blocks};
}

RtlirModule* DescendDefparamPath(RtlirModule* root, const HierPath& path,
                                 const HierPath& writer,
                                 std::vector<PathDescent>& descents,
                                 const ElementIsolator& isolate) {
  DefparamPathEnd reach =
      WalkDefparamPath(root, path, writer, descents, isolate);
  return reach.blocks.empty() ? reach.mod : nullptr;
}

bool EscapesWriterBlock(const DefparamWriterBlocks& blocks,
                        const RtlirModule* writer, RtlirModule* root,
                        const HierPath& steps) {
  auto it = blocks.find(writer);
  if (it == blocks.end()) return false;
  std::vector<PathDescent> descents;
  DescendDefparamPath(root, steps, {}, descents);
  for (const auto& descent : descents) {
    if (descent.from != it->second.holder) continue;
    if (it->second.element != nullptr) {
      return descent.inst->resolved != it->second.element;
    }
    return !PathStartsWith(descent.inst->gen_block_path, it->second.steps);
  }
  return true;
}

}  // namespace delta
