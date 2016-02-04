#define BURSTLEN	4

static size_t get_vlan_offset(struct ether_hdr *eth_hdr, uint16_t *proto)
{

	size_t vlan_offset = 0;
	if(rte_cpu_to_be_16(ETHER_TYPE_VLAN)==*proto){
		struct vlan_hdr *vlan_hdr = (struct vlan_hdr*)(eth_hdr+1);
		vlan_offset = sizeof(struct vlan_hdr);
		*proto = vlan_hdr->eth_proto;
		if(rte_cpu_to_be_16(ETHER_TYPE_VLAN)==*proto){
			vlan_hdr = vlan_hdr + 1;
			*proto = vlan_hdr->eth_proto;
			vlan_offset += sizeof(struct vlan_hdr);
		}
	}	
	return vlan_offset;	

}

static int do_dataplane_job(__attribute__((unused)) void *dummy) {


	uint8_t lcore_id = rte_lcore_id();

	struct rte_mbuf* rcv_pkt_bucket[BURSTLEN];

	while(1) {

		uint32_t rx_pkt_count = rte_eth_rx_burst(ETHDEV_ID, 0, rcv_pkt_bucket, BURSTLEN);
		int i;

		for (i=0; i < rx_pkt_count; i++) {
			uint16_t offset, ether_type;	
			struct rte_mbuf* pkt = rcv_pkt_bucket[i];
				
			rte_prefetch0(rte_pktmbuf_mtod(pkt, void*));
			struct ether_hdr* l2hdr;
			l2hdr = rte_pktmbuf_mtod(pkt, struct ether_hdr*);
			RTE_LOG(INFO, USER1, "=> Packet received... ethtype=%u\n",__bswap_16(l2hdr->ether_type));//__bswap_16

			//=== BEGIN Your code

			//Demo:
			//const struct ether_addr addr2set = {.addr_bytes={0x52,0x00,0x01,0x02,0x03,0x04}};	//52:00:01:02:03:04
			//memcpy(&l2hdr->s_addr, &addr2set, sizeof(struct ether_addr));

			const struct ether_addr task1_addr = {.addr_bytes={0x00,0x15,0x17,0x03,0x00,0x01}};
			const struct ether_addr task2_addr = {.addr_bytes={0x00,0x15,0x17,0x03,0x00,0x02}};
			const struct ether_addr task3_addr = {.addr_bytes={0x00,0x15,0x17,0x03,0x00,0x03}};

			if (memcmp(&task1_addr, &l2hdr->d_addr, sizeof(struct ether_addr)) == 0) {
				//Task 1
				//Copy source address into destination address.	

				memcpy(&l2hdr->d_addr,&l2hdr->s_addr,sizeof(struct ether_addr));
				memcpy(&l2hdr->s_addr,&task1_addr,sizeof(struct ether_addr));

			} else if (memcmp(&task2_addr, &l2hdr->d_addr, sizeof(struct ether_addr)) == 0) {
				//Task 2
			       // RTE_LOG(INFO, USER1, "=> mac address of the packet matched");
				const struct ether_addr addr2set = {.addr_bytes={0x00,0x15,0x17,0x04,0x00,0x02}};
				memcpy(&l2hdr->d_addr,&addr2set,sizeof(struct ether_addr));
				memcpy(&l2hdr->s_addr,&task2_addr,sizeof(struct ether_addr));

				ether_type = __bswap_16(l2hdr->ether_type);

				uint32_t my_ipv4_addr ;

				offset = get_vlan_offset(l2hdr,&ether_type);

				struct ipv4_hdr *ipv4hdr = (struct ipv4_hdr*)((char*)(l2hdr+1)+offset);

				RTE_LOG(INFO,USER1,"IPv4 type %d \n",ipv4hdr->version_ihl);

				if(((__bswap_32(ipv4hdr->dst_addr)>>24) == 192) && (((__bswap_32(ipv4hdr->dst_addr)>>16) & 0x000000ff)==168) &&
 			           (((__bswap_32(ipv4hdr->dst_addr)>>8) & 0x000000ff) == 0)   )
				  {
					RTE_LOG(INFO, USER1, "=> An IP in 192.168.0 format has been found \n");
					uint16_t ip_octet_4 = __bswap_32(ipv4hdr->dst_addr) & 0x000000ff; //This is to be considered while forming the new IP address for insertion later.
					RTE_LOG(INFO,USER1,"=>octet to be inserted is %d \n",ip_octet_4);	

					struct udp_hdr *udp_hdr = (struct udp_hdr*)((char*)ipv4hdr+sizeof(struct ipv4_hdr));
					if(__bswap_16(udp_hdr->dst_port) == 80)
					{
						RTE_LOG(INFO,USER1,"=> UDP Port is recognized as 80 %d\n",__bswap_16(udp_hdr->dst_port));
						//So now all set to modify the packet.
						//Modify the IP information.
						my_ipv4_addr = IPv4(ip_octet_4,1,168,192);
						memcpy(&ipv4hdr->dst_addr,&my_ipv4_addr,sizeof(uint32_t));	

						//Modify the port information.	
						udp_hdr->dst_port = rte_cpu_to_be_16(8080);
						
						//Update Checksum.
						ipv4hdr->hdr_checksum = 0;
						udp_hdr->dgram_cksum=0;
						udp_hdr->dgram_cksum =  rte_ipv4_udptcp_cksum(ipv4hdr, udp_hdr);
						ipv4hdr->hdr_checksum = rte_ipv4_cksum(ipv4hdr);	
						

					}
                                  }

			} else if (memcmp(&task3_addr, &l2hdr->d_addr, sizeof(struct ether_addr)) == 0) {
				//Task 3
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












