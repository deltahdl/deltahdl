#ifndef DELTA_SIMULATOR_DPI_FORMAL_TYPE_H_
#define DELTA_SIMULATOR_DPI_FORMAL_TYPE_H_

#include <cstdint>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/sim_context.h"

namespace delta {

// §H.7.3 and §H.7.4: the type a formal of an imported subroutine crosses the
// interface as, which is not always the type its declaration names.
//
// An enumeration crosses as its base type, through Table H.1. A packed struct
// or union crosses as the one-dimensional packed array of its width, of bit
// where every member is 2-state and of logic otherwise. A name a typedef
// declares crosses as the type it stands for, so `typedef bit [2:0] A` makes a
// formal of type A a three-bit packed array. Any other type crosses as it is
// written.
struct DpiCrossingType {
  DataTypeKind kind = DataTypeKind::kInt;
  // The width of a bit, logic or reg packed array; 0 for every other kind.
  uint32_t width = 0;
  bool is_unsigned = false;
  // Whether a bit, logic or reg type is a packed array rather than the
  // scalar, a one-bit array included (DpiArg::is_packed_array).
  bool is_packed_array = false;
  // The name an unpacked struct or union crosses under (§H.7.5).
  std::string_view type_name = {};
};

// What `declared` crosses as, typedef names resolved through the tables
// `design` records for them (RtlirDesign::type_kinds and its siblings).
DpiCrossingType DpiCrossingTypeOf(const DataType& declared,
                                  const RtlirDesign& design);

// §H.7.3: the unpacked dimensions `dims` a formal's declaration wrote, each as
// its lower and upper bound, outermost first. Empty where there are none, where
// one is open (§35.5.6.1) or where a bound does not fold to a constant.
std::vector<SvActualDimension> DpiSizedUnpackedDimensions(
    const std::vector<Expr*>& dims);

// Sets the type each formal of every import `dpi` holds crosses as, the
// dimensions of each sized unpacked one and the members of each unpacked
// struct or union, whose declaration `ctx` records, for the formals whose
// declaration is known (DpiArg::declaration). Run once the design is lowered
// and before any import is bound to C or called.
void ResolveDpiFormalTypes(DpiRuntime& dpi, const RtlirDesign& design,
                           const SimContext& ctx);

}  // namespace delta

#endif  // DELTA_SIMULATOR_DPI_FORMAL_TYPE_H_
