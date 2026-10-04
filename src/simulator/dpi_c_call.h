// §35.4 and Annex H.8: calling the C function an imported subroutine's linkage
// name resolves to. The prototype of that function is fixed by the import
// declaration alone -- each small input by value as the C type Table H.1 gives
// it, every other argument by reference, and the result by value -- so the
// call is made through a C function generated per import, compiled with the
// system C compiler, which calls the symbol with exactly that prototype. On
// this side the arguments are laid out in the C objects that prototype names
// and read back out of them once the call returns.
#ifndef DELTA_SIMULATOR_DPI_C_CALL_H_
#define DELTA_SIMULATOR_DPI_C_CALL_H_

#include <cstddef>
#include <string>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

namespace delta {

// A generated trampoline: calls `symbol` with the arguments whose C objects
// `args` points at, one per formal in declaration order, and stores the result
// in the C object `result` points at. A formal passed by value is read out of
// its object; one passed by reference is handed the object's address.
using DpiCTrampoline = void (*)(void (*symbol)(), void** args, void* result);

// The name the generated source gives the trampoline of the `index`th import
// it was generated for.
std::string DpiCTrampolineName(std::size_t index);

// Why the import cannot be called in C by this simulator, or empty where it
// can. §H.8 passes a small value, a packed array (integer and time among them)
// and a small result; a formal of any other type -- an unpacked array or open
// array (§35.5.6.1), a struct or union, an enumeration or a type named by a
// typedef -- is laid out in C objects this side does not build yet.
std::string DpiImportNotCallableInC(const DpiRtFunction& import);

// The C source of one trampoline per import of `imports`, the `i`th named
// DpiCTrampolineName(i), each calling its symbol with the prototype §H.8 gives
// that import. Every import is one DpiImportNotCallableInC accepts.
std::string DpiCTrampolineSource(
    const std::vector<const DpiRtFunction*>& imports);

// One import bound to its C function: the declaration's formals and result,
// the function the linkage name resolved to, and the trampoline calling it.
struct DpiCFunction {
  std::vector<DpiArg> formals;
  DataTypeKind result = DataTypeKind::kVoid;
  bool is_task = false;
  void (*symbol)() = nullptr;
  DpiCTrampoline trampoline = nullptr;
};

// §35.7 with §H.8.2: why foreign code cannot call the export `exp` through a
// function this simulator generates, or empty where it can. An open array, a
// struct or union, or a type whose C object is not built here is not passed
// to an exported function yet.
std::string DpiExportNotCallableFromC(const DpiRtExport& exp);

// The function generated beside the forwarders that is handed the one entry
// point every forwarder calls, as `void name(DpiCExportEntry)`.
std::string DpiCExportEntrySetterName();

// The entry point a forwarder calls: the export's position in the source,
// one address per formal -- of the parameter itself where it is passed by
// value, the pointer C passed where it is passed by reference -- and the
// address of the C object the result is left in, null for none.
using DpiCExportEntry = void (*)(int index, void** args, void* result);

// The C source of one forwarder per export of `exports`, the `i`th under its
// linkage name with the prototype §H.8.2 gives it, calling the entry point
// with index i, and of the function that installs that entry point. Every
// export is one DpiExportNotCallableFromC accepts. Empty for none.
std::string DpiCForwarderSource(const std::vector<const DpiRtExport*>& exports);

// §H.8: the value of `formal` held in the C object at `object`, laid out as
// the formal is passed to C.
DpiArgValue DpiValueOfCObject(const DpiArg& formal, const void* object);

// Lays `value` out in the C object at `object` as `formal` is passed to C,
// which is how an export's output reaches its foreign caller.
void DpiStoreInCObject(const DpiArg& formal, const DpiArgValue& value,
                       void* object);

// Lays `value` out in the C object of a result of type `kind` at `result`.
void DpiStoreResultInCObject(DataTypeKind kind, const DpiArgValue& value,
                             void* result);

// §H.8: calls `function` with `args`, one value per formal, each already of
// its formal's type. Every argument is laid out in the C object its passing
// mode names; after the call, the value the C function left in each output and
// inout formal's object replaces that formal's value in `args` (§35.5.1.2),
// and the result comes back as a value of the declared result type.
DpiArgValue CallDpiCFunction(const DpiCFunction& function,
                             std::vector<DpiArgValue>& args);

}  // namespace delta

#endif  // DELTA_SIMULATOR_DPI_C_CALL_H_
