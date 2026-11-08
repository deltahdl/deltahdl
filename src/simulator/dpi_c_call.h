#ifndef DELTA_SIMULATOR_DPI_C_CALL_H_
#define DELTA_SIMULATOR_DPI_C_CALL_H_

#include <cstddef>
#include <string>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

namespace delta {

using DpiCTrampoline = void (*)(void (*symbol)(), void** args, void* result);

std::string DpiCTrampolineName(std::size_t index);

std::string DpiImportNotCallableInC(const DpiRtFunction& import);

std::string DpiCTrampolineSource(
    const std::vector<const DpiRtFunction*>& imports);

struct DpiCFunction {
  std::vector<DpiArg> formals;
  DataTypeKind result = DataTypeKind::kVoid;
  bool is_task = false;
  void (*symbol)() = nullptr;
  DpiCTrampoline trampoline = nullptr;
};

std::string DpiExportNotCallableFromC(const DpiRtExport& exp);

std::string DpiCExportEntrySetterName();

using DpiCExportEntry = void (*)(int index, void** args, void* result);

std::string DpiCForwarderSource(const std::vector<const DpiRtExport*>& exports);

DpiArgValue DpiValueOfCObject(const DpiArg& formal, const void* object);

void DpiStoreInCObject(const DpiArg& formal, const DpiArgValue& value,
                       void* object);

void DpiStoreResultInCObject(DataTypeKind kind, const DpiArgValue& value,
                             void* result);

DpiArgValue CallDpiCFunction(const DpiCFunction& function,
                             std::vector<DpiArgValue>& args);

}  // namespace delta

#endif
