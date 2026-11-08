#include <gtest/gtest.h>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class PortVariablesOfARun : public VpiDesignRun {
 protected:
  static const char* TypespecOf(const char* name) {
    return vpi_get_str(vpiName, vpi_handle(vpiTypespec, By(name)));
  }
};

TEST_F(PortVariablesOfARun, AnAggregatePortVariablesTypespecIsItsTypedefs) {
  Run("typedef struct { int a; int b; } ps_t;\n"
      "typedef union { int a; bit [31:0] b; } pu_t;\n"
      "module top (output ps_t p, output pu_t q); endmodule\n");
  EXPECT_STREQ(TypespecOf("top.p"), "ps_t");
  EXPECT_STREQ(TypespecOf("top.q"), "pu_t");
}

TEST_F(PortVariablesOfARun, AScalarTypedefPortVariablesTypespecIsItsTypedef) {
  Run("typedef enum {A, B} e_t;\n"
      "typedef logic [7:0] byte_t;\n"
      "module top (output e_t p, output byte_t r); endmodule\n");
  EXPECT_STREQ(TypespecOf("top.p"), "e_t");
  EXPECT_STREQ(TypespecOf("top.r"), "byte_t");
}

TEST_F(PortVariablesOfARun, APortExpressionObjectsTypespecIsItsTypedef) {
  Run("typedef struct { int a; int b; } s_t;\n"
      "typedef enum {A, B} e_t;\n"
      "module top (.g(h), .f(k)); output s_t h; output e_t k; endmodule\n");
  EXPECT_STREQ(TypespecOf("top.h"), "s_t");
  EXPECT_STREQ(TypespecOf("top.k"), "e_t");
}

}  // namespace
}  // namespace delta
