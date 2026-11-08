#ifndef DELTA_SIMULATOR_DPI_FORMAL_TYPE_H_
#define DELTA_SIMULATOR_DPI_FORMAL_TYPE_H_

#include <cstdint>
#include <string_view>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/sim_context.h"

namespace delta {

struct DpiCrossingType {
  DataTypeKind kind = DataTypeKind::kInt;
  uint32_t width = 0;
  bool is_unsigned = false;
  bool is_packed_array = false;
  std::string_view type_name = {};
};

DpiCrossingType DpiCrossingTypeOf(const DataType& declared,
                                  const RtlirDesign& design);

DpiArg DpiFormalOfArg(const FunctionArg& arg, const ScopeMap& scope);

ScopeMap DpiParameterScope(const RtlirModule& mod);

std::vector<SvActualDimension> DpiSizedUnpackedDimensions(
    const std::vector<Expr*>& dims, const ScopeMap& scope);

void ResolveDpiFormalTypes(DpiRuntime& dpi, const RtlirDesign& design,
                           const SimContext& ctx);

}  // namespace delta

#endif
