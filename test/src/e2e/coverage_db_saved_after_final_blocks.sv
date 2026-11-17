module t;
  covergroup cg with function sample(bit [1:0] a);
    coverpoint a { bins b[] = {[0:3]}; }
  endgroup
  cg c = new;
  initial begin
    if ($test$plusargs("save")) begin
      $set_coverage_db_name("cov.db");
      c.sample(0);
      $finish;
    end
    $load_coverage_db("cov.db");
    $display("%0.2f", cg::get_coverage());
  end
  final if ($test$plusargs("save")) c.sample(1);
endmodule
