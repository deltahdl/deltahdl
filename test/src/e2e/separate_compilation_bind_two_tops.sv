module sc_two_tops_a;
  initial $display("top a ran");
endmodule

module sc_two_tops_b;
  initial #1 $display("top b ran");
endmodule
