FROM alpine
LABEL maintainer="hello@informal.systems"

EXPOSE 26656 26657 26660

ENTRYPOINT ["/usr/bin/simd"]

CMD ["--home", "/root/.simapp", "start"]

VOLUME [ "/root" ]

COPY gaia/build/simd /usr/bin/simd
COPY simapp/ /root/.simapp
