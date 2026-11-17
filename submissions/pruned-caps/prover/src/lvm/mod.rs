//! The lvm `S` proof (WP-15a: chain/PCS/protocol side): parameters and schedule, tables and layout, links,
//! the null bus, the proof, the stream driver.
pub mod acc;
pub mod bits;
pub mod bus;
/// CAP (S2GB, dev): the V twin of the cap-pruned openings.
pub mod capcheck;
pub mod layout;
pub mod front;
pub mod link;
pub mod loopir;
pub mod m3;
pub mod params;
pub mod prove;
pub mod rec;
pub mod shape;
pub mod stream;
pub mod tables;
pub mod typed;
pub mod typed_dev;
pub mod typed_blob;
pub mod typed_ie;
pub mod typed_lay;
pub mod typed_mb;
pub mod typed_phi;
pub mod typed_prove;
pub mod typed_t;
pub mod wire;
