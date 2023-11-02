module wrapper_top ();
    bit clk;
    localparam MEM_DEPTH = 256;

    wrapper_intf #(.MEM_DEPTH(MEM_DEPTH)) W_intf(clk);

    wrapper DUT (W_intf);

    wrapper_tb TEST (W_intf);

     initial begin
        $readmemh("RAM_data.dat", DUT.MEMORY.mem, 0, 255);
        clk = 1;
        forever 
            #1 clk = ~clk;
    end
endmodule