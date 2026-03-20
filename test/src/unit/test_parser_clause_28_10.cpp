namespace {

TEST(PullSources, EmptyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  pullup ();\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
