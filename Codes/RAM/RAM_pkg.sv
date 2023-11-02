package RAM_pkg;
    class RAM_tr #(parameter MEM_DEPTH = 256);
        localparam ADDR_SIZE = $clog2(MEM_DEPTH);

        rand bit clk, rst_n, rx_valid;
        rand bit [ADDR_SIZE + 1 : 0] rx_data;
        bit [ADDR_SIZE - 1 : 0] wa_idx, ra_idx;
        bit [ADDR_SIZE - 1 : 0] wa_arr [MEM_DEPTH], ra_arr [MEM_DEPTH];
        bit wr_addr_occur, rd_addr_occur;

        constraint rst_c    {rst_n dist {1 :/ 95, 0 :/ 5};}
        constraint rx_c     {rx_valid dist {1 :/ 90, 0 :/ 10};}

        constraint rx_data_c {
            rx_data [ADDR_SIZE + 1]  dist {1 :/ 40, 0 :/ 60};
            rx_data [ADDR_SIZE]      dist {1 :/ 40, 0 :/ 60};

            if (rx_data[ADDR_SIZE + 1] == 0) {
                if (!wr_addr_occur) 
                    rx_data[ADDR_SIZE] == 0;
            }
            else {
                if (!rd_addr_occur) 
                    rx_data[ADDR_SIZE] == 0;
            }

            if (rx_data [ADDR_SIZE + 1 : ADDR_SIZE] == 2'b00)
                rx_data [ADDR_SIZE - 1 : 0] == wa_arr [wa_idx];
            else if (rx_data [ADDR_SIZE + 1 : ADDR_SIZE] == 2'b10)
                rx_data [ADDR_SIZE - 1 : 0] == ra_arr [ra_idx];
        }

        covergroup cvgrp;
            rx_cp:  coverpoint rx_valid;
            rx_data_cp: coverpoint rx_data [ADDR_SIZE + 1 : ADDR_SIZE]; 
            
            wr_addr_cr: cross rx_cp, rx_data_cp iff (rst_n) {
                option.cross_auto_bin_max = 0;
               bins wr_addr_bin = binsof(rx_cp) intersect {1} && binsof(rx_data_cp) intersect {0};
            }
            wr_data_cr: cross rx_cp, rx_data_cp iff (rst_n) {
                option.cross_auto_bin_max = 0;
               bins wr_data_bin = binsof(rx_cp) intersect {1} && binsof(rx_data_cp) intersect {1};
            }
            rd_addr_cr: cross rx_cp, rx_data_cp iff (rst_n) {
                option.cross_auto_bin_max = 0;
               bins rd_addr_bin = binsof(rx_cp) intersect {1} && binsof(rx_data_cp) intersect {2};
            }
            rd_data_cr: cross rx_cp, rx_data_cp iff (rst_n) {
                option.cross_auto_bin_max = 0;
               bins rd_data_bin = binsof(rx_cp) intersect {1} && binsof(rx_data_cp) intersect {3};
            }
        endgroup

        function void post_randomize();
            if (wa_idx == 255) 
                wa_arr.shuffle();
            else if (rx_data [ADDR_SIZE + 1 : ADDR_SIZE] == 2'b00)
                wa_idx++;

            if (ra_idx == 255)
                ra_arr.shuffle();
            else if (rx_data [ADDR_SIZE + 1 : ADDR_SIZE] == 2'b10) 
                ra_idx++;

            if (rx_data [ADDR_SIZE + 1 : ADDR_SIZE] == 2'b00) 
                wr_addr_occur = 1;
            else if (rx_data [ADDR_SIZE + 1 : ADDR_SIZE] == 2'b10) 
                rd_addr_occur = 1;
        endfunction

        function new();
            cvgrp = new;

            for (int i = 0; i < 256; i++) begin
                wa_arr [i] = i;
                ra_arr [i] = i;
            end
            wa_arr.shuffle();
            ra_arr.shuffle();
        endfunction //new()
    endclass //
endpackage