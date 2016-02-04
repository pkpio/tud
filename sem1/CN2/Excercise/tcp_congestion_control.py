"""
Created on Tue Sep 09 13:04:25 2014

@author: frank
"""

import numpy as np
import pylab as pl
from mpltools import style

style.use('ggplot')

class TCP(object):
    """
    This class simulates the TCP congestion control algorithm. 
    It implements the two states slow start and congestion avoidance.
    
    During slow start, the cwnd is increased exponentially
    During congestion avoidance, the cwnd is increased by addition of 
    1 MSS and decreased by a factor of 2.
    
    The simulator assumes to detect congestion by triple acks and not
    by timeouts.
    """
    def __init__(self, MSS = 1, timeout_in_RTT=5):
        self.MSS = MSS
        self.cwnd = self.MSS
        self.ssthresh = 24 #Infty for the first time.
        self.state = "SLOW_START"
        
        #The round in which we are currently
        self.round = 0
        self.has_timeout_happened = False
        self.timeouts = []
        
    def handle_triple_ack(self):
        self.ssthresh = self.cwnd / 2
        self.cwnd = self.ssthresh
        self.state = "CONGESTION_AVOIDANCE"
    
    def add_timeout(self, round, duration):
        self.timeouts.append((round, duration))
        
    def should_timeout(self):
        for cround, duration in self.timeouts:
            if self.round > cround and self.round < cround + duration:
                return True
        return False
    
    def sim(self, bandwith):
        self.round += 1
        if self.should_timeout():
            self.has_timeout_happened = True
        elif self.has_timeout_happened:
            self.ssthres = self.cwnd/2
            self.cwnd = 1
            self.has_timeout_happened = False
        elif self.cwnd >= bandwith:
            self.handle_triple_ack()
        elif self.state == "SLOW_START" and self.cwnd >= self.ssthresh:
            self.state = "CONGESTION_AVOIDANCE"
            self.cwnd += 1
        elif self.state == "SLOW_START":
            self.cwnd = self.cwnd * 2
        elif self.state == "CONGESTION_AVOIDANCE":
            self.cwnd = self.cwnd +1
            
        return self.cwnd

        
np.random.seed(2)


# Toggle here to enable either a static bandwith limit or a varying bandwith over time
# Static Bandwith:
max_bandwith = 50*np.ones(60)

# Changing Bandwith
max_bandwith = np.random.randint(20, 40, 64)

"""
max_bandwidth denotes the bandwith at which a triple duplicate ACK would occur
"""


y = []

tcp = TCP()  

# Use this function to simulate a timeout in a certain round with a certain duartion
#tcp.add_timeout(15, 5)

for b in max_bandwith:
    y.append(tcp.sim(b))


pl.figure(figsize=(16.0, 10.0))
pl.xlim(0,len(max_bandwith))
pl.ylim(0, 70)

l1 = pl.plot(y, label="cwnd size")
l2 = pl.plot(max_bandwith,':', label="Path Capacity")

pl.xlabel("Transmission Round")
pl.ylabel("cwnd size in segments")

pl.legend()

pl.show()