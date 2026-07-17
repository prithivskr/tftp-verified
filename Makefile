ROCQ = rocq compile -Q theories Tftp

.PHONY: all check clean

all: theories/Correctness.vo

theories/Bytes.vo: theories/Bytes.v
	$(ROCQ) $<

theories/Packet.vo: theories/Packet.v theories/Bytes.vo
	$(ROCQ) $<

theories/Spec.vo: theories/Spec.v theories/Packet.vo
	$(ROCQ) $<

theories/Codec.vo: theories/Codec.v theories/Packet.vo
	$(ROCQ) $<

theories/Correctness.vo: theories/Correctness.v theories/Spec.vo theories/Codec.vo
	$(ROCQ) $<

check: all
	rocq check -silent -Q theories Tftp Tftp.Correctness

clean:
	find theories -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '.*.aux' \) -delete
