#pragma once

#include <functional>
#include <vector>

#include "elaborator/elaborator_data.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"

namespace delta {

bool PathStartsWith(const HierPath& path, const HierPath& prefix);

struct PathDescent {
  RtlirModule* from;
  const RtlirModuleInst* inst;
};

using ElementIsolator = std::function<void(RtlirModule&, RtlirModuleInst&)>;

struct DefparamPathEnd {
  RtlirModule* mod;
  HierPath blocks;
};

DefparamPathEnd WalkDefparamPath(RtlirModule* root, const HierPath& path,
                                 const HierPath& writer,
                                 std::vector<PathDescent>& descents,
                                 const ElementIsolator& isolate = {});

RtlirModule* DescendDefparamPath(RtlirModule* root, const HierPath& path,
                                 const HierPath& writer,
                                 std::vector<PathDescent>& descents,
                                 const ElementIsolator& isolate = {});

bool EscapesWriterBlock(const DefparamWriterBlocks& blocks,
                        const RtlirModule* writer, RtlirModule* root,
                        const HierPath& steps);

}  // namespace delta
