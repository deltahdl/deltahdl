#pragma once

namespace delta {

class DiagEngine;
struct ModuleItem;

// A.1.6's extern_tf_declaration: report the parts of an (already-parsed)
// extern prototype that A.2.6's function_prototype and A.2.7's task_prototype
// do not write.
void ValidateExternTfPrototype(DiagEngine& diag, const ModuleItem* item);

}  // namespace delta
