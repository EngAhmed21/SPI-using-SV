module RAM_top ();
    bit clk;
    localparam MEM_DEPTH = 256;

    slave_RAM_intf #(.MEM_DEPTH(MEM_DEPTH)) SR_intf(clk);

    RAM DUT (SR_intf);

    RAM_tb TEST (SR_intf);

    bind RAM RAM_SVA SVA (SR_intf);

     initial begin
        $readmemh("RAM_data.dat", DUT.mem, 0, 255);
        clk = 1;
        forever 
            #1 clk = ~clk;
    end
endmodule