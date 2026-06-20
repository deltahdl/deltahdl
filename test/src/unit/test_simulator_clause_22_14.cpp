#include "helpers_preprocess_and_get.h"

TEST(KeywordVersionSimulation, BeginKeywordsModuleSimulates) {
  auto result = PreprocessAndGet(
      "`begin_keywords \"1800-2023\"\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd99;\n"
      "endmodule\n"
      "`end_keywords\n",
      "result");
  EXPECT_EQ(result, 99u);
}
