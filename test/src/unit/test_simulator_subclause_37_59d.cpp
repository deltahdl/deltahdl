#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.59 detail 5: a design whose casts a case reads the typespecs of.
class CastTypespecsOfARun : public VpiDesignRun {
 protected:
  // The typespec the cast operation `op` converts to; null where `op` is no
  // cast or relates to no typespec.
  static vpiHandle TypespecOfCast(vpiHandle op) {
    if (op == nullptr || vpi_get(vpiOpType, op) != vpiCastOp) return nullptr;
    return vpi_handle(vpiTypespec, op);
  }

  // The typespec kind each of `ops` converts to, 0 for one with none.
  static std::vector<int> KindsCastTo(const std::vector<vpiHandle>& ops) {
    std::vector<int> kinds;
    for (vpiHandle op : ops) {
      vpiHandle typespec = TypespecOfCast(op);
      kinds.push_back(typespec == nullptr ? 0 : vpi_get(vpiType, typespec));
    }
    return kinds;
  }

  // What each statement of the begin-end block each of the top's procedures
  // runs assigns, procedure by procedure and in statement order.
  static std::vector<vpiHandle> AssignedValues() {
    std::vector<vpiHandle> values;
    for (vpiHandle proc : ObjectsOf(vpiProcess, By("top"))) {
      for (vpiHandle stmt : ObjectsOf(vpiStmt, vpi_handle(vpiStmt, proc))) {
        values.push_back(vpi_handle(vpiRhs, stmt));
      }
    }
    return values;
  }

  // §37.14: the higher connection of the port `port` of the instance named
  // `instance`.
  static vpiHandle HighConnOf(const char* instance, const char* port) {
    return vpi_handle(vpiHighConn, Named(vpiPort, By(instance), port));
  }

  // The number of elements each range `typespec` reaches holds, in order.
  static std::vector<int> RangeSizesOf(vpiHandle typespec) {
    std::vector<int> sizes;
    for (vpiHandle range : ObjectsOf(vpiRange, typespec)) {
      sizes.push_back(vpi_get(vpiSize, range));
    }
    return sizes;
  }
};

// With §6.20.2 and §26.3: a cast in a parameter's default value, which its
// module writes, finds a typedef that only a package import makes visible,
// reached from the parameter through vpiExpr (§37.28 detail 3).
TEST_F(CastTypespecsOfARun, ACastInAParameterDefaultFindsAnImportedTypedef) {
  Run("package pk; typedef bit [5:0] six_t; endpackage\n"
      "module sub; import pk::*; parameter logic [5:0] P = six_t'(8'hff);\n"
      "endmodule\n"
      "module top; sub u(); endmodule\n");
  vpiHandle typespec = TypespecOfCast(
      vpi_handle(vpiExpr, Named(vpiParameter, By("top.u"), "P")));
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiBitTypespec);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "six_t");
}

// With §23.3.2: a cast in a port connection, which the instantiating module
// writes, finds a typedef a package declares, named through the package or
// made visible by an import (§26.3), one the compilation unit declares
// (§3.12.1), and one the first top declares, though the top's instance is
// keyed under its name rather than the empty prefix it writes with.
TEST_F(CastTypespecsOfARun, ACastInAPortConnectionFindsItsTypedef) {
  Run("package pk; typedef logic [3:0] nib_t; typedef bit [5:0] six_t;\n"
      "endpackage\n"
      "typedef shortint unit_t;\n"
      "module sub(input logic [15:0] p); endmodule\n"
      "module top; import pk::*; typedef byte own_t; logic [7:0] x;\n"
      "  sub a(.p(pk::nib_t'(x))); sub b(.p(six_t'(x)));\n"
      "  sub c(.p(unit_t'(x))); sub d(.p(own_t'(x)));\n"
      "endmodule\n");
  const std::vector<int> kKinds = {vpiLogicTypespec, vpiBitTypespec,
                                   vpiShortIntTypespec, vpiByteTypespec};
  EXPECT_EQ(KindsCastTo({HighConnOf("top.a", "p"), HighConnOf("top.b", "p"),
                         HighConnOf("top.c", "p"), HighConnOf("top.d", "p")}),
            kKinds);
}

// With §8.23 and §6.23: a cast to a type reference naming a class's typedef
// through the class, and a cast naming it so directly, convert to that
// typedef's typespec, which the class defn holds.
TEST_F(CastTypespecsOfARun, ACastToAClassScopedTypedefHasItsTypespec) {
  Run("module top; class C; typedef bit [3:0] T; endclass\n"
      "  logic [7:0] x; logic [3:0] y;\n"
      "  initial begin y = type(C::T)'(x); y = C::T'(x); end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kValues = AssignedValues();
  ASSERT_EQ(kValues.size(), 2U);
  for (vpiHandle value : kValues) {
    vpiHandle typespec = TypespecOfCast(value);
    ASSERT_NE(typespec, nullptr);
    EXPECT_EQ(vpi_get(vpiType, typespec), vpiBitTypespec);
    EXPECT_STREQ(vpi_get_str(vpiName, typespec), "T");
  }
}

// With §6.23 and §37.25 detail 8: a cast to a type reference writing packed
// dimensions after a typedef's name converts to a typespec of those
// dimensions over the typedef's, ranging over both (detail 10).
TEST_F(CastTypespecsOfARun, ACastToADimensionedTypeReferenceRangesOverBoth) {
  Run("module top; typedef bit [3:0] nib_t; logic [15:0] v; logic [7:0] d;\n"
      "  initial begin d = type(nib_t [1:0])'(v); end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kValues = AssignedValues();
  ASSERT_EQ(kValues.size(), 1U);
  vpiHandle typespec = TypespecOfCast(kValues.front());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiBitTypespec);
  EXPECT_EQ(RangeSizesOf(typespec), (std::vector<int>{2, 4}));
}

}  // namespace
}  // namespace delta
