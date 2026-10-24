#pragma once

namespace delta {

class DiagEngine;
struct DataType;
struct ModuleItem;

// Whether `result`, a function prototype's result as the parser reads it,
// writes no type: an implicit_data_type, which is a bare signing, bare packed
// dimensions or nothing at all. A.2.6's function_prototype takes a
// data_type_or_void, which admits none of these, and a type reference, which
// the parser holds as an implicit type carrying its expression, is one of
// A.2.2.1's data_types.
bool IsImplicitResultType(const DataType& result);

// A.1.6's extern_tf_declaration: report the parts of an (already-parsed)
// extern prototype that A.2.6's function_prototype and A.2.7's task_prototype
// do not write.
void ValidateExternTfPrototype(DiagEngine& diag, const ModuleItem* item);

// A.1.9's class_method: report the parts of an (already-parsed) `extern` or
// `pure virtual` method prototype of a class that A.2.6's function_prototype
// and A.2.7's task_prototype do not write.
void ValidateClassMethodPrototype(DiagEngine& diag, const ModuleItem* item);

}  // namespace delta
