#include <gtest/gtest.h>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.17 Variables, read off the VPI model a run builds from an elaborated
// design: the typespec a variable a port declares relates to, which is the
// typedef the port's declaration wrote, as a body declaration's is.

class PortVariablesOfARun : public VpiDesignRun {
 protected:
  // The name of the typespec the variable `name` relates to; null for none.
  static const char* TypespecOf(const char* name) {
    return vpi_get_str(vpiName, vpi_handle(vpiTypespec, By(name)));
  }
};

// The variable a structure or union port with no port kind declares
// (§23.2.2.3)...
TEST_F(PortVariablesOfARun, AnAggregatePortVariablesTypespecIsItsTypedefs) {
  Run("typedef struct { int a; int b; } ps_t;\n"
      "typedef union { int a; bit [31:0] b; } pu_t;\n"
      "module top (output ps_t p, output pu_t q); endmodule\n");
  EXPECT_STREQ(TypespecOf("top.p"), "ps_t");
  EXPECT_STREQ(TypespecOf("top.q"), "pu_t");
}

// ...the variable an output port of any other typedef type declares...
TEST_F(PortVariablesOfARun, AScalarTypedefPortVariablesTypespecIsItsTypedef) {
  Run("typedef enum {A, B} e_t;\n"
      "typedef logic [7:0] byte_t;\n"
      "module top (output e_t p, output byte_t r); endmodule\n");
  EXPECT_STREQ(TypespecOf("top.p"), "e_t");
  EXPECT_STREQ(TypespecOf("top.r"), "byte_t");
}

// ...and the variable a port declaration declares for an object a non-ANSI
// port expression names (§23.2.2.1).
TEST_F(PortVariablesOfARun, APortExpressionObjectsTypespecIsItsTypedef) {
  Run("typedef struct { int a; int b; } s_t;\n"
      "typedef enum {A, B} e_t;\n"
      "module top (.g(h), .f(k)); output s_t h; output e_t k; endmodule\n");
  EXPECT_STREQ(TypespecOf("top.h"), "s_t");
  EXPECT_STREQ(TypespecOf("top.k"), "e_t");
}

}  // namespace
}  // namespace delta
