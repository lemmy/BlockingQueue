#!/usr/bin/env Rscript
args = commandArgs(trailingOnly=TRUE)

library(ggplot2)
library(stringr)
library(svglite)

data <- read.csv(header=TRUE, sep = ",", file = args[1])

## Poor-mans version of grouping the data according to 'P', 'B', and 'C' by concatenating the 0-padded values.
data <- within(data, config <- paste(sep = "/", str_pad(data$P, 3, pad = "0"), str_pad(data$C, 3, pad = "0"),str_pad(data$B, 3, pad = "0")))

## Group data by the 'config' column and calculate mean for 'over' and 'under'.
ag.means <- aggregate(cbind(data$over, data$under), by=list(config=data$config), FUN=mean)
names(ag.means)[names(ag.means)=="V1"] <- "mean_over"
names(ag.means)[names(ag.means)=="V2"] <- "mean_under"

## Group data by the 'config' column and calculate standard deviation for 'over' and 'under'.
ag.sd <- aggregate(cbind(data$over, data$under), by=list(config=data$config), FUN=sd)
names(ag.sd)[names(ag.sd)=="V1"] <- "sd_over"
names(ag.sd)[names(ag.sd)=="V2"] <- "sd_under"

## Merge the two data frames by the common 'config' column.
df <- merge(ag.means, ag.sd)

p <- ggplot(df, aes(x = config, y = mean_over, fill = config)) +
  geom_errorbar(aes(ymin=mean_over-sd_over, ymax=mean_over+sd_over), width=.2, position=position_dodge(.9)) +
  geom_bar(stat = "identity") +
  geom_bar(aes(x= config, y = mean_under, fill=config), stat="identity",position="dodge") +
  geom_errorbar(aes(ymin=mean_under-sd_under, ymax=mean_under+sd_under), width=.2, position=position_dodge(.9)) +
  geom_hline(yintercept = 0, alpha = 0.3) +
  #scale_x_discrete(guide = guide_axis(n.dodge=3))+
  scale_x_discrete(guide = guide_axis(check.overlap = TRUE))+
  coord_flip() +
  theme_minimal() +
  theme(legend.position = "none") +
  labs(
    x = "Configuration |P|/|C|/B",
    y = "Average under- and over-provisioning of consumers (positive |ac|>|ap|)",
    title = paste(
      "Traces:", nrow(data), format(Sys.time(), "(%a %b %d %X %Y)")
    )
  )
ggsave(gsub(".csv$", ".svg", args[1]), plot = last_plot(), bg = "white", device = "svg")