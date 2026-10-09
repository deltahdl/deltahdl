#pragma once

#include <string_view>

#include "parser/ast_stmt.h"

namespace delta {

// §17.3: a checker instantiated in procedural code, a procedural checker
// instance: the statement that instantiates it and the name its instance
// carries in the module, the generate prefix included, as
// RtlirModuleInst::inst_name has it. RtlirProcess holds one per such
// instance. Moved out of rtlir.h, which stood at the size the
// assert-no-oversized-source-files job fails at.
struct ProceduralCheckerSite {
  const Stmt* stmt = nullptr;
  std::string_view inst_name;
};

}  // namespace delta
