FROM alpine
LABEL maintainer="hello@informal.systems"

EXPOSE 26656 26657 26660

ENTRYPOINT ["/usr/bin/gaiad"]

CMD ["start"]

VOLUME [ "/root" ]

COPY gaia/build/gaiad /usr/bin/gaiad
COPY gaia/build/chain_a/node0/gaiad /root/.gaiad
COPY gaia/build/chain_a/node0/gaiacli/key_seed.json /root/key_seed.json
