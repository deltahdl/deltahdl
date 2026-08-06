// §21.4.1 Reading packed data — parse acceptance of the destination forms the
// subclause adds to the $readmemb / $readmemh memory_name operand: unpacked
// arrays of packed elements, dynamic arrays, queues, and associative arrays.
// The subclause defines no BNF of its own (Syntax 21-12 belongs to §21.4);
// these tests only pin down that each destination form reaches the parser as
// an ordinary call operand alongside its real declaration syntax.
#include "fixture_program.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Descriptive suite name for this file's tests; the underlying fixture is the
// shared program-parse fixture.
using ReadmemDestinationParse = ProgramTestParse;

// §21.4.1: a packed-struct element type, a dynamic array, a queue, and an
// associative array each parse as a $readmem destination.
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

// §21.4.1: enumerated, wildcard, and string index types on the associative
// destination all parse; whether the index is integral is judged later, at
// run time, not by the call grammar.
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

// §21.4.1 / §21.4: start and finish address arguments follow the container
// destinations too, in literal and parameter form.
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
