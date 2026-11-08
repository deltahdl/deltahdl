#include <gtest/gtest.h>

#include "fixture_program.h"

using namespace delta;

namespace {

using ReadmemDestinationParse = ProgramTestParse;

TEST_F(ReadmemDestinationParse, PackedDataDestinationFormsParse) {
  auto* unit = Parse(R"(
    module m;
      typedef struct packed { logic [3:0] hi; logic [11:0] lo; } st_t;
      st_t smem [0:3];
      logic [7:0] dyn [];
      logic [7:0] q [$];
      logic [7:0] aa [int];
      initial begin
        $readmemh("s.mem", smem);
        $readmemh("d.mem", dyn);
        $readmemb("q.mem", q);
        $readmemh("a.mem", aa);
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(ReadmemDestinationParse, AssocIndexTypeFormsParse) {
  auto* unit = Parse(R"(
    module m;
      typedef enum {RED = 2, GREEN = 5} color_t;
      logic [7:0] ae [color_t];
      logic [7:0] aw [*];
      logic [7:0] as [string];
      initial begin
        $readmemh("e.mem", ae);
        $readmemh("w.mem", aw);
        $readmemh("s.mem", as);
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(ReadmemDestinationParse,
       ContainerDestinationsWithAddressArgumentsParse) {
  auto* unit = Parse(R"(
    module m;
      parameter int START = 5;
      logic [7:0] aa [int];
      logic [7:0] q [$];
      initial begin
        $readmemh("a.mem", aa, START);
        $readmemh("q.mem", q, 9, 7);
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

}  // namespace
