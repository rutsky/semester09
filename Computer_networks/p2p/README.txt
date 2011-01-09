Network emulation test model.

Copyright (C) 2010, 2011  Vladimir Rutsky <altsysrq@gmail.com>


Implements folowing network stack:

--- transport or any above layer ---
  packet transfer -
                                     [src, dest, data] 
        - delivered between services clients located around network;

--- network layer ---
  datagram transfer
                           [protocol, src, dest, data]
        - delivered between network hosts (routers);

--- channel layer ---
  frames transfer -
     [type, id, last, len, [.......data bytes[]......], CRC]

  raw frames transfer
    [[........................bytes[]......................] EndOfFrame]
        - transfer of grouped bytes between two directly connected hosts;

--- physical layer ---
  byte transfer
    (byte)
        - stream of bytes between two directly connected hosts.


True network topology model:

      H       H       H
      |       |       |
  H - N - R - N - R - N - H
      |       |       |
      H       R       H
              |
          H - N - H
              |
              H

Hosts (H) and routers (R) connected to networks (N) and communicating
through networks.


For simpler RIP implementation was used following network topology model:

 (N,H,H,H)R ----- R(N,H,H,H)
            \   /
              R
              (N,H,H,H)

Only networks connected to leaf routers interfaces valued as networks,
and each router has exactly one of them. All routers connected directly to
each other.

Data is send from router to router assuming that in true model it is sent
from/to networks connected to according router.

Routing table is reduced to:
  (destination router, next router)
When router receives packet (src, dest, data) it looks up next router in 
routing table and retransmits packet there.
