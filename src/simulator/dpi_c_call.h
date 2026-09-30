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

// §H.8: calls `function` with `args`, one value per formal, each already of
// its formal's type. Every argument is laid out in the C object its passing
// mode names; after the call, the value the C function left in each output and
// inout formal's object replaces that formal's value in `args` (§35.5.1.2),
// and the result comes back as a value of the declared result type.
DpiArgValue CallDpiCFunction(const DpiCFunction& function,
                             std::vector<DpiArgValue>& args);

}  // namespace delta

#endif  // DELTA_SIMULATOR_DPI_C_CALL_H_
