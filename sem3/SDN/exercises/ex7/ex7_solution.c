#define BURSTLEN	4

static int do_dataplane_job(__attribute__((unused)) void *dummy) {

	/* BEGIN Added for task 3 */

	typedef struct  __attribute__((__packed__)) {
		struct ether_addr d_addr;
		struct ether_addr s_addr;
		uint16_t ethertype;
		uint16_t preamble;
		uint64_t sequenceNo;
	} task_3_encap;

	/* END Added for task 3 */


	uint8_t lcore_id = rte_lcore_id();

	struct rte_mbuf* rcv_pkt_bucket[BURSTLEN];

	uint64_t task_3_sequenceNo = 0;	//Added for Task 3

	while(1) {		

		uint32_t rx_pkt_count = rte_eth_rx_burst(ETHDEV_ID, 0, rcv_pkt_bucket, BURSTLEN);
		int i;
	
		for (i=0; i < rx_pkt_count; i++) {
			struct rte_mbuf* pkt = rcv_pkt_bucket[i];

			rte_prefetch0(rte_pktmbuf_mtod(pkt, void*));
			struct ether_hdr* l2hdr;			
			l2hdr = rte_pktmbuf_mtod(pkt, struct ether_hdr*);
			RTE_LOG(INFO, USER1, "=> Packet received... ethtype=%u\n", __bswap_16(l2hdr->ether_type));

			//=== BEGIN Your code

			//Demo:
			//const struct ether_addr addr2set = {.addr_bytes={0x52,0x00,0x01,0x02,0x03,0x04}};	//52:00:01:02:03:04
			//memcpy(&l2hdr->s_addr, &addr2set, sizeof(struct ether_addr));

			const struct ether_addr task1_addr = {.addr_bytes={0x00,0x15,0x17,0x03,0x00,0x01}};
			const struct ether_addr task2_addr = {.addr_bytes={0x00,0x15,0x17,0x03,0x00,0x02}};
			const struct ether_addr task3_addr = {.addr_bytes={0x00,0x15,0x17,0x03,0x00,0x03}};

			const struct ether_addr task2_target_addr = {.addr_bytes={0x00,0x15,0x17,0x04,0x00,0x02}};
			const struct ether_addr task3_tunnelendpoint_addr = {.addr_bytes={0x00,0x15,0x17,0x04,0x00,0x03}};
			
			if (memcmp(&task1_addr, &l2hdr->d_addr, sizeof(struct ether_addr)) == 0) {
				//Task 1
				RTE_LOG(INFO, USER1, "=> Packet received for task 1, swapping header\n");

				struct ether_addr tmp;
				memcpy(&tmp, &l2hdr->d_addr, sizeof(struct ether_addr));
				memcpy(&l2hdr->d_addr, &l2hdr->s_addr, sizeof(struct ether_addr));
				memcpy(&l2hdr->s_addr, &tmp, sizeof(struct ether_addr));

			} else if (memcmp(&task2_addr, &l2hdr->d_addr, sizeof(struct ether_addr)) == 0) {
				//Task 2
				RTE_LOG(INFO, USER1, "=> Packet received for task 2, changing the MAC, IP address and port number...\n");

				memcpy(&l2hdr->d_addr, &task2_target_addr, sizeof(struct ether_addr));
				memcpy(&l2hdr->s_addr, &task2_addr, sizeof(struct ether_addr));

				struct ipv4_hdr* iphdr;
				iphdr = rte_pktmbuf_mtod_offset(pkt, struct ipv4_hdr*, sizeof(struct ether_hdr));
				
				struct udp_hdr* udphdr;
				udphdr = rte_pktmbuf_mtod_offset(pkt, struct udp_hdr*, sizeof(struct ether_hdr)+sizeof(struct ipv4_hdr));				

				uint16_t destport = __bswap_16(udphdr->dst_port);

				if (destport != 80) {
					//Not the target port
					printf("Not our port: %u.\n", destport);
					rte_pktmbuf_free(pkt);
					continue;
				}

				//Changing IP address:
				if ((iphdr->dst_addr & 0x00ff0000) != 0x00000000) {	//"Filters" the third octet (zeroes the rest) with a bit-wise and, and compares the result with 0. Thus, checks if the third octet is not zero. Note we are in little-endian representation, thus we have to count the octets from right to left.
					//Not the target IP range
					rte_pktmbuf_free(pkt);
					continue;
				}
				
				iphdr->dst_addr += 0x00010000; //Increment the third octet by 1.
				
				//Changing port
				udphdr->dst_port = __bswap_16(8080);

				iphdr->time_to_live--;

				iphdr->hdr_checksum = 0;
				iphdr->hdr_checksum = rte_ipv4_cksum(iphdr);

			} else if (memcmp(&task3_addr, &l2hdr->d_addr, sizeof(struct ether_addr)) == 0) {

				//[dstMAC|srcMAC|ethtype] [Payload]
				//[dstMAC|srcMAC|0x0803] [0x3434|64-byte unsigned byte offset number, incrementing] [Payload: whole original ethernet header.]

				//Task 3
				RTE_LOG(INFO, USER1, "=> Packet received for task 3, tunneling, headroom=%u\n", rte_pktmbuf_headroom(pkt));

				//See the definition of the task_3_encap struct at the top.
				task_3_encap* encapHdr = (task_3_encap*) rte_pktmbuf_prepend(pkt, sizeof(task_3_encap));

				//The check below is not necessary for a correct solution.
				if (encapHdr == NULL) {
					RTE_LOG(INFO, USER1, "ERROR: Could not prepend header\n");
					rte_pktmbuf_free(pkt);
					continue;
				}

				memcpy(&encapHdr->d_addr, &task3_tunnelendpoint_addr, sizeof(struct ether_addr));
				memcpy(&encapHdr->s_addr, &task3_addr, sizeof(struct ether_addr));
				encapHdr->ethertype = __bswap_16(0x0803);
				encapHdr->preamble = __bswap_16(0x3434);
				encapHdr->sequenceNo = __bswap_64(task_3_sequenceNo);

				task_3_sequenceNo++;

			
	
			} else {
				RTE_LOG(INFO, USER1, "=> Packet for unknown target received, dropping...\n");
				rte_pktmbuf_free(pkt);
				continue;
			}

			//=== END Your code
	
			int retrn = rte_eth_tx_burst(ETHDEV_ID, 0, &rcv_pkt_bucket[i], 1);
				//For better performance, you could also bulk-send multiple packets here.
			if (retrn != 1) {
				RTE_LOG(INFO, USER1, "    TX burst failed with error code %i.\n", retrn);
			}

		}

	}
	
	return 0;


}












